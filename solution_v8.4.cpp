#include "td/utils/Gzip.h"
#include "td/utils/lz4.h"
#include "td/utils/base64.h"
#include "vm/boc.h"
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <queue>
#include <memory>
#include <random>
#include <vector>

using namespace std;

string b64d(string s) { return td::base64_decode(s).move_as_ok(); }

uint8_t brev8(uint8_t x) {
  uint8_t y = 0;
  for (int i = 0; i < 8; ++i) y = y * 2 + x % 2, x /= 2;
  return y;
}

struct BitI {
  BitI(string t = ""): s(t), cb{0} { reverse(s.begin(), s.end()); }
  BitI(BitI& from, int nbits): s(from.s.substr(from.s.size() - (from.cb + nbits + 7) / 8)), cb{from.cb} {
    s[0] &= -1 << (-from.cb - nbits & 7);
    from.s.resize(from.s.size() - (from.cb + nbits) / 8);
    from.cb = from.cb + nbits & 7;
  }
  
  template <typename T>
  auto& rdi(T& x, int bytes = 1) { x = 0; while (bytes--) x = x * 256 + uint8_t(s.back()), s.pop_back(); return x; }
  template <typename T>
  auto& rdbi(T& x, int bits) { x = 0; while (bits--) x = x *2 + rdb(); return x; }
  void rbflush() { if (cb) cb = 0, s.pop_back();  }
  bool rdb() { bool x = s.back() & 128 >> cb++; if (cb == 8) cb = 0, s.pop_back(); return x; }
  bool rdbtz() { return s.size()? rdb(): 0; }
  int getbpos() { return s.size() * 8 - cb; }

  string s;
  int cb;
};

struct BitO {
  BitO(): s(), cb{8} { }
  
  void wti(uint32_t x, int bytes = 1) { while (bytes--) s += char(x >> bytes * 8 & 255); }
  void wtbi(uint64_t x, int bits) { while (bits--) wtb(x >> bits & 1); }
  void wbflush() { if (cb != 8) cb = 8;  }
  void wtb(bool x) { if (cb == 8) cb = 0, s += '\0'; s.back() ^= x << 7 - cb++; }
  int getbpos() { return s.size() * 8 - 8 + cb; }

  void append(BitO& from) {
    int nbits = from.getbpos();
    for (BitI tmp(from.s); nbits--; ) wtb(tmp.rdb());
  }

  string s;
  int cb;
};

template <int freq_bits_ = 60>
struct FreqTable {
  static constexpr int freq_bits = freq_bits_;

  FreqTable(vector<int64_t> f): f(f), cf(f.size() + 1) {
    partial_sum(f.begin(), f.end(), cf.begin() + 1);
    sf = cf.back();
  }

  void upd(int i) { }
  int64_t getcf(int i) { return cf[i]; }
  int64_t getsf() { return sf; }
  int getsym(int64_t v) { return upper_bound(cf.begin(), cf.end(), v) - cf.begin() - 1; }

private:
  vector<int64_t> f, cf;
  int64_t sf;
};

template <typename T>
struct Fenw {
  vector<T> v;
  int n, mxo;

  Fenw(int n): v(n), n{n}, mxo{1} { while (2 * mxo < n) mxo *= 2; }
  Fenw(vector<T> u): Fenw(u.size()) { for (int i = 0; i < n; ++i) if (v[i] += u[i], (i | i + 1) < n) v[i | i + 1] += v[i]; }

  void add(int i, T x) { for (; i < n; i |= i + 1) v[i] += x; }
  T que(int i) { T x{}; for (; i; i &= i - 1) x += v[i - 1]; return x; }

  int ubo(T x) {
    T y{};
    int i{};
    for (int k = mxo; k; k /= 2) if (i + k < n && y + v[i + k - 1] <= x) y += v[(i |= k) - 1];
    return i + 1;
  }
};

auto genfreq = [](int n, auto f) {
  vector<decay_t<decltype(f(0))>> v;
  for (int i = n; i--; ) v[i] = f(i);
  return v;
};

template <typename T, int freq_bits_ = 60>
struct CountingTable {
  static constexpr int freq_bits = freq_bits_;

  CountingTable(vector<T> f, T step): cf{f}, step{step} { sf = cf.que(f.size()); }

  void upd(int i) { cf.add(i, step), sf += step; }
  void upd(int i, int step) { cf.add(i, step), sf += step; }
  T getcf(int i) { return cf.que(i); }
  T getsf() { return sf; }
  int getsym(T x) { return cf.ubo(x) - 1; }

private:
  Fenw<T> cf;
  T sf, step;
};

template <typename T, int freq_bits_ = 60>
struct SmoothCountingTable {
  static constexpr int freq_bits = freq_bits_;

  SmoothCountingTable(vector<T> f, T step, int smooth): cf{f}, step{step}, smooth{smooth} { sf = cf.que(f.size()); }

  void upd(int i) {
    for (int j = max(i - smooth, 0); j < min(i + smooth, (int)cf.v.size()); ++j) {
      cf.add(j, step - step * abs(i - j) / smooth), sf += step - step * abs(i - j) / smooth;
      // cf.add(j, step - step * abs(i - j)  * abs(i - j) / smooth / smooth), sf += step - step * abs(i - j) * abs(i - j) / smooth / smooth;
      // cf.add(j, step * smooth / (abs(i - j) + smooth)), sf += step* smooth / (abs(i - j) + smooth);
    }
  }
  T getcf(int i) { return cf.que(i); }
  T getsf() { return sf; }
  int getsym(T x) { return cf.ubo(x) - 1; }

private:
  Fenw<T> cf;
  T sf, step;
  int smooth;
};

template <int freq_bits_ = 60>
struct SubsetTable {
  static constexpr int freq_bits = freq_bits_;

  SubsetTable(int64_t n, int k): n{n}, k{k}, sf{1ll << freq_bits_} { }

  void upd(int64_t i) { n = i, --k; }//cerr << "upd st " << i << ' ' << n << ' ' << k << '\n'; }
  int64_t getsf() { return sf; }

  int64_t getcf(int64_t i) {
    if (!k || i == n) return i? sf: 0;
    if (i == k - 1) return 0;
    int64_t t = n - i;
    double B = 1. / sf * 8;
    double a = exp(lgamma(1 + i) - lgamma(1 + i - k) + (lgamma(1 + n - k) - lgamma(1 + n)));
    int64_t res = (a + B * i) / (1 + B * (n - k + 1) * 1.1) * (sf - 1);
    // cerr << "getcf st " << a << ' ' << B << ' ' << res * 1. / sf << ' ' << i << ' ' << n << ' ' << k << '\n';
    return res;
  }

  int64_t getsym(int64_t x) {
    if (!k) return 0;
    int64_t l = k - 1, r = n;
    while (r > l + 1) (getcf((l + r) / 2) <= x? l: r) = (l + r) / 2;
    // cerr << "getsym st " << x << ' ' << sf << ' ' << x * 1. / sf << ' ' << l << ' ' << n << ' ' << k << '\n'; 
    return l;
  }

private:
  int64_t n;
  int k;
  int64_t sf;
};

struct u128 {
  using u64 = uint64_t;
  using u32 = uint32_t;

  u64 hi, lo;

  static u128 mul(u64 x, u64 y) {
    u32 a = x >> 32, b = x;
    u32 c = y >> 32, d = y;
    u64 ac = (u64)a * c;
    u64 ad = (u64)a * d;
    u64 bc = (u64)b * c;
    u64 bd = (u64)b * d;
    u64 carry = (u64)(u32)ad + (u64)(u32)bc + (bd >> 32);
    u64 hi = ac + (ad >> 32) + (bc >> 32) + (carry >> 32);
    u64 lo = (ad << 32) + (bc << 32) + bd;
    return {hi, lo};
  }

  u64 operator/(u64 x) {
    u64 rat, res;
    asm(
      "divq %4; \n\t"
      : "=a" (rat), "=d" (res)
      : "d" (hi), "a" (lo), "r" (x)
    );
    return rat;
  }

  u128& dec() { return hi -= !lo--, *this; }
};

template <typename Coder, typename FreqTable>
struct ArithmCoder {
  static constexpr int64_t range_bits = 62, N = 1ull << range_bits, S = 1ull << FreqTable::freq_bits;
  FreqTable f;
  int64_t l, r;

  ArithmCoder(FreqTable f) : f(f), l{}, r{N - 1} {
    assert(f.getsf() <= S);
  }

  void upd(int64_t i) {
    auto d = r - l + 1;
    r = l + u128::mul(f.getcf(i + 1), d) / f.getsf() - 1;
    l = l + u128::mul(f.getcf(i), d) / f.getsf();
    assert(r > l);
    while (!((l ^ r) & N / 2)) ((Coder&)*this).shift(), l = 2 * l & N - 1, r = 2 * r & N - 1 | 1;
    while (((l & ~r) & N / 4)) ((Coder&)*this).tweak(), l = 2 * l ^ N / 2, r = 2 * r ^ N ^ N / 2 | 1;
    f.upd(i);
  }
};

template <typename FreqTable>
struct ArithmEncoder: ArithmCoder<ArithmEncoder<FreqTable>, FreqTable> {
  using Base = ArithmCoder<ArithmEncoder<FreqTable>, FreqTable>;
  BitO& out;
  int& rbits;
  int sbits, d;

  ArithmEncoder(FreqTable f, BitO& out, int& rbits): Base{f}, out{out}, rbits{rbits}, sbits{out.getbpos()}, d{} { }
  void shift() { for (out.wtb(Base::r >= Base::N / 2); d; --d) out.wtb(Base::l < Base::N / 2); }
  void tweak() { ++d; }
  void write(int64_t i) { Base::upd(i); }
  void finish() { if (~d) d = -1, out.wtb(1), rbits = out.getbpos() - sbits; }
  ~ArithmEncoder() { finish(); }
};

// TODO: avoid the need to encode nbits by encoding nsym and ungetting extra bits? or will noise after the end of stream break last few characters?
template <typename FreqTable>
struct ArithmDecoder: ArithmCoder<ArithmDecoder<FreqTable>, FreqTable> {
  using Base = ArithmCoder<ArithmDecoder<FreqTable>, FreqTable>;
  BitI in;
  int64_t code;

  ArithmDecoder(FreqTable f, BitI& inp, int nbits): Base{f}, in{inp, nbits}, code{} {
    for (int i = Base::range_bits; i--; ) code = code * 2 + in.rdbtz();
  }

  void shift() { code = code << 1 & Base::N - 1 | in.rdbtz(); }
  void tweak() { code = code & Base::N / 2 | code << 1 & Base::N / 2 - 1 | in.rdbtz(); }
  int64_t read() { int64_t x = Base::f.getsym(u128::mul(code - Base::l + 1, Base::f.getsf()).dec() / (Base::r - Base::l + 1)); return Base::upd(x), x; }
};

template <typename T, typename F>
struct Context {
  T t; F f;
  Context(T t, F f): t(move(t)), f(move(f)) { }
  ~Context() { f(move(t)); }
  operator bool() { return 1; }
};

namespace cmk666SAIS {
#define For(i, j, k) for ( int i = (j) ; i <= (k) ; i++ )
#define Fol(i, j, k) for ( int i = (j) ; i >= (k) ; i-- )
	template < class IT > inline void induced_sort(int n, int m, IT s, int o,
												   int *val, int *ty, int *cnt, int *sa)
	{
		int *c = cnt + m + 1; fill(sa, sa + n + 1, 0), copy(cnt, c, c);
		Fol(i, o, 0) sa[--c[s[val[i]]]] = val[i];
		copy(cnt, cnt + m, c + 1);
		For(i, 0, n) if ( sa[i] && !ty[sa[i] - 1] ) sa[c[s[sa[i] - 1]]++] = sa[i] - 1;
		copy(cnt, c, c);
		Fol(i, n, 0) if ( sa[i] &&  ty[sa[i] - 1] ) sa[--c[s[sa[i] - 1]]] = sa[i] - 1;
	}
	template < class IT > inline bool lms_equal(int x, int y, IT s, int *ty)
	{
		if ( s[x] != s[y] ) return false;
		while ( s[++x] == s[++y] && ty[x] == ty[y] ) if ( ty[x] == 2 ) return true;
		return false;
	}
	template < class IT > inline void sa_is(int n, int m, IT s, int *ty, int *lms, int *cnt, int *sa)
	{
		int o = -1, c = -1, *t = sa;
		ty[n] = 1; Fol(i, n - 1, 0) ty[i] = s[i] == s[i + 1] ? ty[i + 1] : s[i] < s[i + 1];
		fill(cnt, cnt + m + 1, 0); For(i, 0, n) cnt[s[i]]++; partial_sum(cnt, cnt + m + 1, cnt);
		For(i, 1, n) if ( !ty[i - 1] && ty[i] ) ty[i] = 2, lms[++o] = i;
		induced_sort(n, m, s, o, lms, ty, cnt, sa);
		For(i, 0, n) if ( ty[sa[i]] == 2 ) *t++ = sa[i];
		For(i, 0, o) c += c <= 0 || !lms_equal(sa[i], sa[i - 1], s, ty), t[sa[i] >> 1] = c;
		For(i, 0, o) t[i] = t[lms[i] >> 1];
		if ( c < o ) sa_is(o, c, t, ty + n + 1, lms + o + 1, cnt + m + 1, sa);
		else For(i, 0, o) sa[t[i]] = i;
		For(i, 0, o) lms[o + 1 + i] = lms[sa[i]];
		induced_sort(n, m, s, o, lms + o + 1, ty, cnt, sa);
	}
	template < class IT > void suffix_sort(int n, IT s, int *sa)
	{
		using T = typename iterator_traits < IT >::value_type;
    vector<T> t(n + 1);
    vector<int> ty(n * 2 + 2), lms(n + 1), cnt(n * 2 + 2);
		auto o = minmax_element(s + 1, s + n + 1); int d = *o.first - 1, m = *o.second - d;
		For(i, 1, n) t[i - 1] = s[i] - d; t[n] = 0;
		sa_is(n, m, &t[0], &ty[0], &lms[0], &cnt[0], sa); For(i, 1, n) sa[i]++;
	}
#undef For
#undef Fol
}

struct SA {
  vector<int> sa, lcp, x;

  SA(string s): sa(s.size() + 1), lcp(s.size() + 1), x(s.size() + 1) {
    int n = s.size();
    s = '\0' + s;
    cmk666SAIS::suffix_sort(n, s.begin(), &sa[0]);
    s.erase(s.begin());
    for (int i = n; ~i; --i) x[sa[i] -= !!i] = i;
		for (int i = 0, k = 0, j; i < n; lcp[x[i++]] = k)
			for (k && k--, j = sa[x[i] - 1]; max(i, j) + k < n &&
					s[i + k] == s[j + k]; k++);
    sa.erase(sa.begin());
    // x.erase(x.begin());
    x.pop_back();
    lcp.erase(lcp.begin());
    lcp.erase(lcp.begin());
    for (auto& x: x) --x;
  }
};

struct DSU {
  vector<int> p;
  vector<array<int, 2>> h;

  DSU(int n): p(n, -1) { }

  int getp(int v) { return p[v] < 0? v * 2: getp(p[v] / 2) ^ p[v] & 1; }
  int getppc(int v) { return p[v] < 0? v * 2: p[v] = getppc(p[v] / 2) ^ p[v] & 1; }
  
  bool uni(int u, int v, int x) {
    if ((u = getp(u)) / 2 == (v = getp(v)) / 2) return 0;
    x ^= u + v & 1, u /= 2, v /= 2;
    if (p[u] < p[v]) swap(u, v);
    h.push_back({u, p[u]});
    p[v] += p[u], p[u] = v * 2 + x;
    return 1;
  }

  void rollback(int t) {
    while (h.size() > t) {
      auto [u, pu] = h.back(); h.pop_back();
      p[p[u] / 2] -= pu, p[u] = pu;
    }
  }
};

template <typename T>
vector<int> lis(vector<int> v, T cmp, int d = 0) {
  vector<int> ind(v.size()), val(v.size(), max(1e9, -1e9, cmp)), prev(v.size()), res;
  for (int i = 0; i < v.size(); ++i) {
    int j = lower_bound(val.begin(), val.end(), v[i] - d, cmp) - val.begin();
    ind[j] = i, val[j] = v[i], prev[i] = j? ind[j - 1]: -1;
  }
  for (int i = ind[lower_bound(val.begin(), val.end(), max(9e8, -9e8, cmp), cmp) - val.begin() - 1]; ~i; i = prev[i]) res.push_back(i);
  return {res.rbegin(), res.rend()};
}

pair<vector<int>, vector<int>> unmerge(vector<int> v, vector<int> pos) {
  vector<int> u, w;
  for (int i = 0, j = 0; i < v.size(); ++i) {
    if (j < pos.size() && pos[j] == i) u.push_back(v[i]), ++j;
    else w.push_back(v[i]);
  }
  return {u, w};
}

void subsetencode(int64_t n, vector<int64_t> v, BitO& out, BitO& outb, bool withrep, bool partition) {
  assert(is_sorted(v.begin(), v.end()));
  if (withrep) {
    n += v.size() - 1;
    for (int i = 0; i < v.size(); ++i) v[i] += i;
  }
  if (!partition) {
    int nbits;
    reverse(v.begin(), v.end());
    for (ArithmEncoder ac{SubsetTable{n, (int)v.size()}, outb, nbits}; auto& v: v) ac.write(v);//, cerr << v << ' '; cerr << '\n';
    out.wti(nbits, 4);
    cerr << "bpi@" << n << ',' << v.size() << ": " << nbits * 1. / v.size() << '\n';
    return;
  }
  const int pb = 64 - __builtin_clzll(n), pc = 32;
  vector<double> dp(2 * v.size() + 2, 1e99);
  vector<int64_t> bnd(dp.size());
  for (int i = 0; i < dp.size(); ++i) bnd[i] = i % 2? i == dp.size() - 1? n: v[i / 2]: i? v[i / 2 - 1] + 1: 0;
  vector<int> from(dp.size());
  dp[0] = dp[1] = 0;
  for (int i = 2; i < dp.size(); ++i)
  for (int j = 0; j < i; ++j) {
    auto n = bnd[i] - bnd[j];
    int k = i / 2 - j / 2;
    double cost = lgamma(n + 1) - lgamma(n - k + 1) - lgamma(k + 1) + (j? pb: 0) + pc;
    if (i == dp.size() - 1) {
      cerr << dp[i] << ' ' << dp[j] + cost << '\n';
    }
    if (dp[i] > dp[j] + cost) dp[i] = dp[j] + cost, from[i] = j;
  }
  vector<int64_t> sel;
  for (int i = dp.size() - 1; i; ) if (i = from[i]) sel.push_back(bnd[i]);
  out.wti(sel.size(), 4);
  for (auto x: sel) outb.wtbi(x, pb);
  sel.push_back(n);
  for (int64_t p = 0, i = 0; auto x: sel) {
    vector<int64_t> cur;
    while (i < v.size() && v[i] < x) cur.push_back(v[i++] - p);
    out.wti(cur.size(), 4);
    if (cur.size()) subsetencode(x - p, cur, out, outb, 0, 0);
    p = x;
  }
}

vector<int64_t> subsetdecode(int64_t n, int k, BitI& in, BitI& inb, bool withrep, bool partition) {
  if (withrep) n += k - 1;
  vector<int64_t> v(k);
  if (!partition) {
    int nbits; in.rdi(nbits, 4);
    for (ArithmDecoder ac{SubsetTable{n, (int)v.size()}, inb, nbits}; auto& v: v) v = ac.read();//, cerr << v << ' '; cerr << '\n';
    reverse(v.begin(), v.end());
  } else {
    const int pb = 64 - __builtin_clzll(n);
    int nbnd; in.rdi(nbnd, 4);
    vector<int64_t> sel(nbnd);
    for (auto& x: sel) inb.rdbi(x, pb);
    sel.push_back(n);
    for (int64_t p = 0, i = 0; auto x: sel) {
      int sz; in.rdi(sz, 4);
      if (sz) {
        auto u = subsetdecode(x - p, sz, in, inb, 0, 0);
        for (auto x: u) v[i++] = x + p;
      }
      p = x;
    }
  }
  if (withrep) for (int i = 0; i < v.size(); ++i) v[i] -= i;
  return v;
}

double logc(int n, int k) { return (lgamma(n + 1) - lgamma(n - k + 1) - lgamma(k + 1)) / log(2); }

int64_t multiway_delta_prior(int i, int mx) {
  // auto cdf = [&](double x) { return pow(1 - pow(1 - x / mx, 3.8), .54); };
  // auto cdf = [&](double x) { return sqrtf(1 - powf(1 - x / mx, 4)); };
  auto cdf = [&](double x) { auto t = 1 - x / mx; return sqrt(1 - (t * t) * (t * t)); };
  auto _012 = .76, _3 = 2.49, _45 = 2.63, _6 = 3.55;
  auto t = __builtin_ctz(i | 64);
  return (i < 17? 0: (cdf(i + 1) - cdf(i)) * 1e7 * (t < 3? _012: t < 4? _3: t < 6? _45: _6)) + 1;
}

vector<int> numways{2, };
void multiwayencode(string s, BitO& out, BitO& outb) {
  // int sz = s.size();
  // out.wti(sz, 4);
  // for (auto c: s) out.wti(c);
  // return;
  string bits, bits2;
  for (auto c: s) for (int k = 8; k--; ) bits += char(c >> k & 1);
  cerr << bits.size() << '\n';
  SA sa(bits);
  DSU dsu(bits.size());
  // if (bits.size() > 9 << 18) numways.pop_back();
  // if (bits.size() > 12 << 18) numways.pop_back();
  // if (bits.size() > 13 << 18) numways.pop_back();
  // const int lmax = 1 << 10, pi = 8, pd = 32 - __builtin_clz(bits.size() - 1) - 4, pl = 10, pt = 0;
  const int lmax = 1 << 10, pi = 32 - __builtin_clz(bits.size() - 1), pd = pi, pl = 10, pt = 0;
  const vector<int> lazies(numways.back() - 1, 0);
  auto eae = [&](int w, int l, int c) { return -l * (w - 1) - 2 * (w == 2) + pl + pi + pd * (w - 1) + pt + c; };
  auto prio = [&](int w, int l, int c) { return -((eae(w, l, c) + lazies[w - 2]) * 48 + 0 * c) / (w - 1) - eae(w, l, c); };
  vector<vector<array<int, 6>>> repeats(prio(numways.back(), lmax, 0) + 1);
  priority_queue hugerepeats([](auto& a, auto& b) { return a[0] < b[0]; }, vector<array<int, 6>>{});
  vector<pair<int, vector<int>>> ops;
  int ent = bits.size();
  cerr << bits.size() << '\n';
  auto placematch = [&](int w, int cc, int l, int dl, int dr, int v) {
    int p = prio(w, l - dl, cc);
    if (p < 0 || p >= repeats.size()) hugerepeats.push({p, w, l, dl, dr, v});
    else repeats[p].push_back({p, w, l, dl, dr, v});
  };
  auto takematch = [&, p = (int)repeats.size() - 1]() mutable -> array<int, 6> {
    while (1) {
      if (hugerepeats.size() && (hugerepeats.top()[0] >= p || p < 0)) {
        auto x = hugerepeats.top(); hugerepeats.pop();
        return x;
      } else if (p < 0) return {-1 << 30, 0, 0, 0, 0, 0};
      else if (repeats[p].empty()) --p;
      else {
        auto x = repeats[p].back(); repeats[p].pop_back();
        return x;
      }
    }
  };
  for (int i = 0; i < numways.size(); ++i) {
    int w = numways[i];
    for (int i = w - 2; i < sa.lcp.size(); ++i) {
      bool mx = 0;
      int l = 1e9, mxl = -1e9;
      for (int j = 0; j < w - 1; ++j) l = min(l, sa.lcp[i - j]), mxl = max(mxl, sa.lcp[i - j]);
      for (int j = -1; j < w - 1; ++j) {
        mx |= !sa.sa[i - j];
        if (!mx && ~j) mx |= bits[sa.sa[i + 1] - 1] != bits[sa.sa[i - j] - 1];
      }
      if (mx && eae(w, l, 0) < 0) {
        int p = prio(w, l, 0);
        placematch(w, 0, l, 0, 0, i - w + 2);
      }
    }
  }
  while (1) {
    auto [p, w, l, dl, dr, i] = takematch();
    if (p == -1 << 30) break;
    auto every2 = [&](int t) {
      for (int j = 1; j < w; ++j) if (dsu.getppc(sa.sa[i + j] + t) / 2 != dsu.getppc(sa.sa[i] + t) / 2) return 0;
      return 1;
    };
    while (l > dl && every2(l - 1)) --l, ++dr;
    while (l > dl && every2(dl)) ++dl;
    int dent = eae(w, l - dl, 0);
    if (dent >= 0) { continue; }
    if (p > prio(w, l - dl, 0)) { placematch(w, 0, l, dl, dr, i); continue; }
    dsu.h.clear();
    int t = l;
    int cc = 0;
    while (t-- > dl) for (int j = 1; j < w; ++j) cc += !dsu.uni(sa.sa[i + j] + t, sa.sa[i] + t, 0);
    if (w == 2 && min(sa.sa[i], sa.sa[i + 1]) > 0 && max(sa.sa[i], sa.sa[i + 1]) + l + dr < bits.size()) cc += !dsu.uni(sa.sa[i + 1] - 1, sa.sa[i] - 1, 1) + !dsu.uni(sa.sa[i + 1] + l + dr, sa.sa[i] + l + dr, 1);
    dent = eae(w, l - dl, cc);
    if (dent >= 0) { dsu.rollback(0); continue; }
    if (p != prio(w, l - dl, cc)) { placematch(w, cc, l, dl, dr, i); dsu.rollback(0); continue; }
    // , cerr << w << " dec prio " << p - prio(w, l - dl, cc) << ' ' << -dent << ' ' << l << '\n'
    for (int t = dl; t < l; ++t) for (int j = 0; j < w; ++j) dsu.getppc(sa.sa[i + j] + t);
    ent += dent;
    vector<int> v;
    for (int j = 0; j < w; ++j) v.push_back(sa.sa[i + j]);
    sort(v.begin(), v.end());
    // cerr << w << " compress " << l - dl << ' ' << dl << ' ' << dr << ' ' << cc << ' ' << ent << ' ' << -dent << ' ';
    // for (int i = 0; i < w; ++i) cerr << v[i] << ' ';
    // for (int i = 1; i < w; ++i) cerr << ' ' << v[i] - v[i - 1];
    // cerr << '\n';
    ops.push_back({l + dr, move(v)});
  }
  out.wti(bits.size(), 4);
  out.wti(ops.size(), 4);
  for (auto& [l, v]: ops) sort(v.rbegin(), v.rend());
  sort(ops.begin(), ops.end(), [](auto& a, auto& b) { return a.second[0] > b.second[0];  });
  int acbits;
  // if (ArithmEncoder ac{CountingTable<int64_t>(vector<int64_t>(numways.size(), 1), 1), outb, acbits}; 1)
  // for (auto& [l, v]: ops) ac.write(find(numways.begin(), numways.end(), v.size()) - numways.begin());
  // out.wti(acbits, 4);
  for (int i = -1; auto& [l, v]: ops) if (++i, l >= lmax) {
    outb.wtb(1);
    outb.wtbi(i, 32 - __builtin_clz(ops.size() - 1 | 1));
    outb.wtbi(0, 32 - __builtin_clz(l / lmax) - 1);
    outb.wtbi(l, 32 - __builtin_clz(l));
    cerr << "oversize " << l << '\n';
  }
  outb.wtb(0);
  int ssz = 0;
  if (ArithmEncoder ac{SmoothCountingTable<int64_t>(vector<int64_t>(lmax, 1e2), 1e3, 10), outb, acbits}; 1)
  for (auto& [l, v]: ops) {
    if (l < lmax) ac.write(l - 1);
    ssz += v.size();
  }
  out.wti(acbits, 4);
  if (ArithmEncoder ac{SubsetTable{0, 0}, outb, acbits}; 1)
  for (int i = 0, p = bits.size() - 1; auto [l, v]: ops) {
    // ac.f = SubsetTable(p + 1, (ssz + ops.size() - i++) / 2);
    ac.f = SubsetTable(p + 1, ops.size() - i++);
    ac.write(v[0]);
    ssz -= v.size();
    p = v[0];
    ac.f = SubsetTable(p, 1);
    ac.write(v[1]);
  }
  out.wti(acbits, 4);
  // vector<int64_t> prior(bits.size()), cnt(bits.size());
  // for (int i = 0; i < bits.size(); ++i) prior[i] = multiway_delta_prior(i, bits.size());
  // if (ArithmEncoder ac{CountingTable<int64_t>(prior, 0), outb, acbits}; 1)
  // for (auto [l, v]: ops)
  // for (int i = 0; ++i < v.size(); ) {
  //   int d = v[i - 1] - v[i];
  //   ac.write(d);
  //   ++cnt[d];
  //   ac.f.upd(d, prior[d] * (cnt[d] < 4? 8: 1));
  // }
  // out.wti(acbits, 4);
  vector<int> minx(bits.size(), bits.size());
  for (int i = bits.size(); i--; ) minx[dsu.getppc(i) / 2] = i;
  sort(minx.begin(), minx.end());
  for (auto x: minx) if (x < bits.size()) outb.wtb(bits[x]);
  outb.wbflush();
  cerr << bits.size() << ' ' << ops.size() << '\n';
}

string multiwaydecode(BitI& in, BitI& inb) {
  // int sz; in.rdi(sz, 4);
  // string res(sz, '\0');
  // for (auto& c: res) in.rdi(c);
  // return res;
  int nbits, nops;
  in.rdi(nbits, 4), in.rdi(nops, 4);
  // if (nbits > 9 << 18) numways.pop_back();
  // if (nbits > 12 << 18) numways.pop_back();
  // if (nbits > 13 << 18) numways.pop_back();
  cerr << nbits << ' ' << nops << '\n';
  vector<pair<int, vector<int>>> ops(nops);
  int ssz = 0, acbits;
  // in.rdi(acbits, 4);
  // if (ArithmDecoder ac{CountingTable<int64_t>(vector<int64_t>(numways.size(), 1), 1), inb, acbits}; 1)
  // for (auto& [l, v]: ops) v.resize(numways[ac.read()]);
  for (auto& [l, v]: ops) v.resize(2);
  while (inb.rdb()) {
    int i, k = 0;
    inb.rdbi(i, 32 - __builtin_clz(ops.size() - 1 | 1));
    while (!inb.rdb()) ++k;
    inb.rdbi(ops[i].first, k + 10) |= 1 << k + 10;
    cerr << "oversize " << ops[i].first << '\n';
  }
  in.rdi(acbits, 4);
  if (ArithmDecoder ac{SmoothCountingTable<int64_t>(vector<int64_t>(1 << 10, 1e2), 1e3, 10), inb, acbits}; 1)
  for (auto& [l, v]: ops) {
    if (!l) l = ac.read() + 1;
    ssz += v.size();
  }
  in.rdi(acbits, 4);
  if (ArithmDecoder ac{SubsetTable{0, 0}, inb, acbits}; 1)
  for (int i = 0, p = nbits - 1; auto& [l, v]: ops) {
    // ac.f = SubsetTable(p + 1, (ssz + ops.size() - i++) / 2);
    ac.f = SubsetTable(p + 1, ops.size() - i++);
    v[0] = ac.read();
    ssz -= v.size();
    p = v[0];
    ac.f = SubsetTable(p, 1);
    v[1] = ac.read();
  }
  // vector<int64_t> prior(nbits), cnt(nbits);
  // for (int i = 0; i < nbits; ++i) prior[i] = multiway_delta_prior(i, nbits);
  // in.rdi(acbits, 4);
  // if (ArithmDecoder ac{CountingTable<int64_t>(prior, 0), inb, acbits}; 1)
  // for (auto& [l, v]: ops)
  // for (int i = 0; ++i < v.size(); ) {
  //   int d = ac.read();
  //   v[i] = v[i - 1] - d;
  //   ++cnt[d];
  //   ac.f.upd(d, prior[d] * (cnt[d] < 4? 8: 1));
  // }
  DSU dsu(nbits);
  for (auto [l, v]: ops) {
    if (v.size() == 2 && v[1] && v[0] + l < nbits) dsu.uni(v[0] - 1, v[1] - 1, 1), dsu.uni(v[0] + l, v[1] + l, 1);
    while (l--) for (int i = v.size(); i--; ) dsu.uni(v[0] + l, v[i] + l, 0);
  }
  vector<int> minx(nbits, nbits);
  for (int i = nbits; i--; ) minx[dsu.getppc(i) / 2] = i;
  sort(minx.begin(), minx.end());
  string bits(nbits, '\0');
  for (auto x: minx) if (x < nbits) bits[dsu.getppc(x) / 2] = inb.rdb() ^ dsu.getppc(x) & 1;
  for (int i = nbits; i--; ) bits[i] = bits[dsu.getppc(i) / 2] ^ dsu.getppc(i) & 1;
  string s(bits.size() / 8, '\0');
  for (int i = 0; auto& c: s) for (int k = 8; k--; ) c |= bits[i++] << k;
  inb.rbflush();
  return s;
}

string allc = b64d("");
vector<string> allcsp;
map<string, int> c2i;
string allh = b64d("");
map<string, int> h2i;

bool not_master;

struct DAG {
  BitI in, inb; BitO out, outb;
  vector<vector<char>> data;
  vector<int> refd, bitd, lvl, spec, nref;
  vector<vector<int>> to;
  vector<int> contsz, contbit;
  vector<array<int, 2>> conte;
  int f, pi, ps, nc, nr, z, sc, ir;
  int origsz;
  
  
  int nbytes(uint32_t x) { int n = 1; while (1ull << n * 8 <= x) ++n; return n; }
  void rdh(bool sh) { in.rdi(f, sh? 0: 4), in.rdi(f), pi = f & 7, in.rdi(ps), in.rdi(nc, pi), sh ?: in.rdi(nr, pi), sh ?: in.rdi(z, pi), in.rdi(sc, ps), sh ?: in.rdi(ir, pi); data.resize(nc), refd.resize(nc), bitd.resize(nc), lvl.resize(nc), spec.resize(nc), nref.resize(nc), to.resize(nc); }
  void wth(bool sh) { pi = nbytes(nc), f = f & ~7 | pi, ps = nbytes(sc), nr = 1, z = 0, ir = 0; sh? void(): out.wti(0xb5ee9c72, 4), out.wti(f), out.wti(ps), out.wti(nc, pi), sh? void(): out.wti(nr, pi), sh? void(): out.wti(z, pi), out.wti(sc, ps), sh? void(): out.wti(ir, pi); }
  void splitrefd(int i) { auto r = refd[i], b = bitd[i]; lvl[i] = r >> 5, spec[i] = r & 8? b & 2? b / 35 + 1: 1: 0, nref[i] = r & 7, data[i].resize(bitd[i] + 1 >> 1); }

#define $i$ for (int i = 0; i < nc; ++i)
#define $o$ for (auto i: ord)
#define $pi$ for (int p = 0, pp = 0, i = 0; i < nc; ++i)
#define $po$ for (int p = 0, pp = 0; auto i: ord)
  void rdaos() {
    origsz = in.s.size();
    rdh(0);
    assert(pi <= 2);
    $i$ {
      in.rdi(refd[i]), in.rdi(bitd[i]), splitrefd(i);
      to[i].resize(nref[i]);
      for (int j = 0; j * 2 < bitd[i]; ++j) in.rdi(data[i][j]);
      for (int j = 0; j < nref[i]; ++j) in.rdi(to[i][j], pi);
    }
    // contract();
    vector<uint64_t> h(nc);
    for (int i = nc; i--; ) {
      uint64_t t = refd[i] * 256 + bitd[i];
      for (auto x: to[i]) t += h[x];
      h[i] = t * 1617825673;
    }
    // $i$ if (lvl[i] >= 1) cerr << spec[i] << ' ' << i << ' ' << nref[i] << ' ' << data[i].size() << '\n';
    // cerr << h[0] << '\n';
  }

  void wtaos() {
    vector<uint64_t> h(nc);
    for (int i = nc; i--; ) {
      uint64_t t = refd[i] * 256 + bitd[i];
      for (auto x: to[i]) t += h[x];
      h[i] = t * 1617825673;
      // h[i] = refd[i] * 256 + bitd[i];
      // for (auto x: to[i]) h[i] = h[i] * 1617825673 + h[x];
    }
    // cerr << h[0] << '\n';
    // uncontract();
    wth(0);
    $i$ {
      out.wti(refd[i]), out.wti(bitd[i]);
      for (int j = 0; j * 2 < bitd[i]; ++j) out.wti(data[i][j]);
      // cerr << i << ' ' << nref[i] << ' ' << to[i].size() << '\n';
      for (int j = 0; j < nref[i]; ++j) out.wti(to[i][j], pi);
    }
  }

  void relabel(vector<int> label) {
    vector<int> ilabel(nc);
    vector<char> vis(nc);
    $i$ ilabel[label[i]] = i;
    $i$ for (int j = i, k; !vis[j]; j = k) if (vis[j] = 1, !vis[k = ilabel[j]]) {
      swap(data[j], data[k]);
      swap(refd[j], refd[k]);
      swap(bitd[j], bitd[k]);
      swap(lvl[j], lvl[k]);
      swap(spec[j], spec[k]);
      swap(nref[j], nref[k]);
      swap(to[j], to[k]);
    }
    $i$ for (auto& x: to[i]) x = label[x];
  }

  vector<int> label_canon() {
    vector<int> label(nc);
    int tout = 0;
    auto dfs = [&](auto dfs, int v) -> void {
      label[v] = 1;
      for (auto u: to[v]) if (!label[u]) dfs(dfs, u);
      label[v] = ++tout;
    };
    dfs(dfs, 0);
    int c = tout;
    for (auto& x: label) x = x? tout - x: c++;
    relabel(label);
    return label;
  }

  vector<int> label_compact() {
    vector<int> label(nc);
    vector<char> vis(nc), tvis(nc);
    auto cntrch = [&](auto cntrch, int v) -> int {
      tvis[v] = 1;
      int cv = 1;
      for (auto u: to[v]) if (!tvis[u]) cv += cntrch(cntrch, u);
      return cv;
    };
    int tout = 0;
    auto dfs = [&](auto dfs, int v) -> void {
      vis[v] = 1;
      vector<int> ind, szsub;
      for (int i = -1; auto u: to[v]) if (++i, !vis[u]) ind.push_back(i), tvis = vis, szsub.push_back(cntrch(cntrch, u)); else szsub.push_back(-1);
      sort(ind.rbegin(), ind.rend(), [&](int i, int j) { return szsub[i] < szsub[j]; });
      for (auto i: ind) if (auto u = to[v][i]; !vis[u]) dfs(dfs, u);
      label[v] = ++tout;
    };
    dfs(dfs, 0);
    int c = tout;
    for (auto& x: label) x = x? tout - x: c++;
    relabel(label);
    return label;
  }

  void contract() {
    label_canon();
    vector<vector<int>> from(nc);
    vector<int> label(nc);
    $i$ for (auto& j: to[i]) from[j].push_back(i);
    vector<int> inde(nc);
    int nv = nc;
    for (int sz = conte.size() + 1; sz != conte.size() && (sz = conte.size(), 1); )
    $pi$ for (auto& j: to[i]) if (from[j].size() == 2) {
      vector<int> A, B, C;
      int a = i, b = from[j][0] ^ from[j][1] ^ a;
      if (from[a].size() != 1 || from[b].size() != 1 || a == b) continue;
      int a0 = a, pa = from[a0][0], ia = find(to[pa].begin(), to[pa].end(), a0) - to[pa].begin();
      int b0 = b, pb = from[b0][0], ib = find(to[pb].begin(), to[pb].end(), b0) - to[pb].begin();
      while (1) {
        if (to[a].size() != 2 || to[b].size() != 2 || from[a].size() > 1 || from[b].size() > 1) break;
        int c = -1;
        if (to[a][0] == to[b][0]) c = to[a][0];
        if (to[a][1] == to[b][1]) c = to[a][1];
        if (!~c || from[c].size() != 2 || to[c].size()) break;
        int na = to[a][0] ^ to[a][1] ^ c, nb = to[b][0] ^ to[b][1] ^ c;
        A.push_back(a), B.push_back(b), C.push_back(c), 
        a = na, b = nb;
      }
      if (A.size() < 2) continue;
      vector<int> D{A};
      D.insert(D.end(), B.begin(), B.end());
      D.insert(D.end(), C.begin(), C.end());
      D.insert(D.end(), {pa, pb, a, b});
      sort(D.begin(), D.end());
      if (unique(D.begin(), D.end()) != D.end()) continue;
      contsz.push_back(A.size());
      to[pa][ia] = a;
      to[pb][ib] = b;
      nv -= A.size() * 3;
      // cerr << pa << ' ' << a << ' ' << pb << ' ' << b << '\n';
      // cerr << refd[pb] << ' ' << bitd[pb] << ' ' << +data[pb][3] << " -> " << refd[b] << ' ' << bitd[b] << ' ' << +data[b][3] << "\n";
      // cerr << refd[pb] << ' ' << bitd[pb] << ' ' << +data[pb][3] << " -> " << refd[b] << ' ' << bitd[b] << ' ' << +data[b][3] << "\n";
      fill(label.begin(), label.end(), 0);
      int tpa = pa, tpb = pb;
      for (int i = 0; i < A.size(); ++i) {
        // cerr << refd[tpa] << ' ' << bitd[tpa] << ' ' << +data[tpa][3] << " -> " << refd[A[i]] << ' ' << bitd[A[i]] << ' ' << +data[A[i]][3] << "\n";
        // cerr << refd[tpb] << ' ' << bitd[tpb] << ' ' << +data[tpb][3] << " -> " << refd[B[i]] << ' ' << bitd[B[i]] << ' ' << +data[B[i]][3] << "\n";
        tpa = A[i];
        tpb = B[i];
        contbit.push_back(to[A[i]][1] == C[i]);
        to[A[i]] = {};
        label[A[i]] = nv++;
        to[B[i]] = {};
        label[B[i]] = nv++;
        to[C[i]] = {};
        label[C[i]] = nv++;
      }
      // cerr << refd[tpa] << ' ' << bitd[tpa] << ' ' << +data[tpa][3] << " -> " << refd[a] << ' ' << bitd[a] << ' ' << +data[a][3] << "\n";
      // cerr << refd[tpb] << ' ' << bitd[tpb] << ' ' << +data[tpb][3] << " -> " << refd[b] << ' ' << bitd[b] << ' ' << +data[b][3] << "\n";
      nv -= A.size() * 3;
      for (int i = 0, j = 0; i < nc; ++i, j += j == nv? A.size() * 3: 0) if (!label[i]) label[i] = j++;
      pa = label[pa], pb = label[pb];
      relabel(label);
      auto lbl = label_canon();
      $pi$ inde[i] = p, p += to[i].size();
      conte.push_back({inde[lbl[pa]] + ia, inde[lbl[pb]] + ib});
      $i$ from[i].clear();
      $i$ for (auto& j: to[i]) from[j].push_back(i);
    }
    done:;
    // for (int i = nc - contbit.size() * 3; i < nc; i += 1 + ((nc - i) % 3 == 2)) cerr << refd[i] << ' '; cerr << '\n';
    // for (int i = nc - contbit.size() * 3; i < nc; i += 1 + ((nc - i) % 3 == 2)) cerr << bitd[i] << ' '; cerr << '\n';
    // for (int i = nc - contbit.size() * 3; i < nc; i += 1 + ((nc - i) % 3 == 2)) cerr << (!spec[i] && data[i].size()? data[i][0]: 999) << ' '; cerr << '\n';
    // for (int i = nc - contbit.size() * 3 + 2; i < nc; i += 3) cerr << refd[i] << ' '; cerr << '\n';
    // for (int i = nc - contbit.size() * 3 + 2; i < nc; i += 3) cerr << bitd[i] << ' '; cerr << '\n';
    // for (int i = nc - contbit.size() * 3 + 2; i < nc; i += 3) cerr << (!spec[i] && data[i].size()? data[i][0]: 999) << ' '; cerr << '\n';
    // for (int i = 0, j = 0; i < nc; ++i) if (!label[i]) label[i] = j++;
    // relabel(label);
    label_compact();
  }

  void uncontract() {
    label_canon();
    vector<vector<int>> from(nc);
    $i$ for (auto& j: to[i]) from[j].push_back(i);
    vector<int> inde(nc);
    int nv = nc - contbit.size() * 3, nb = contbit.size();
    for (int i = conte.size(); i--; ) {
      label_canon();
      auto [a, b] = conte[i];
      $pi$ inde[i] = p, p += to[i].size();
      $i$ from[i].clear();
      $i$ for (auto& j: to[i]) from[j].push_back(i);
      int pa = upper_bound(inde.begin(), inde.end(), a) - inde.begin() - 1;
      int pb = upper_bound(inde.begin(), inde.end(), b) - inde.begin() - 1;
      int ia = a - inde[pa], ib = b - inde[pb];
      a = to[pa][ia], b = to[pb][ib];
      nb -= contsz[i];
      for (int j = 0; j < contsz[i]; ++j) {
        // cerr << i << ' ' << j << ' ' << pa << ' ' << to[pa].size() << ' ' << ia << '\n';
        // cerr << i << ' ' << j << ' ' << pb << ' ' << to[pb].size() << ' ' << ib << '\n';
        assert(ia < to[pa].size());
        assert(ib < to[pb].size());
        // cerr << refd[pa] << ' ' << bitd[pa] << ' ' << +data[pa][3] << " -> " << refd[a] << ' ' << bitd[a] << ' ' << +data[a][3] << "\n";
        // cerr << refd[pb] << ' ' << bitd[pb] << ' ' << +data[pb][3] << " -> " << refd[b] << ' ' << bitd[b] << ' ' << +data[b][3] << "\n";
        int bit = contbit[nb++];
        to[pa][ia] = nv, to[nv++].push_back(a);
        to[pb][ib] = nv, to[nv++].push_back(b);
        to[nv - 2].insert(to[nv - 2].begin() + bit, nv);
        to[nv - 1].insert(to[nv - 1].begin() + bit, nv);
        ia = ib = !bit;
        pa = nv - 2, pb = nv++ - 1;
      }
      // cerr << refd[pa] << ' ' << bitd[pa] << ' ' << +data[pa][3] << " -> " << refd[a] << ' ' << bitd[a] << ' ' << +data[a][3] << "\n";
      // cerr << refd[pb] << ' ' << bitd[pb] << ' ' << +data[pb][3] << " -> " << refd[b] << ' ' << bitd[b] << ' ' << +data[b][3] << "\n";
      nb -= contsz[i];
    }
    assert(nv == nc);
    label_canon();
  }

  void wtdoag() {
    vector<int> sd, hm, href;
    vector<int> remref(nc);
    $i$ for (auto x: to[i]) ++remref[x];
    vector<int> roots{0};
    vector<int> label(nc);
    $i$ label[i] = i;
    for (int i = 0; roots.size(); ++i) {
      auto r = roots.back(); roots.pop_back();
      label[r] = i;
      sd.push_back(0);
      hm.push_back(0);
      for (int j = -1; auto x: to[r]) if (++j, --remref[x]) href.push_back(x), hm[i] |= 1 << j; else roots.push_back(x), ++sd[i];
    }
    for (auto& x: href) x = label[x];
    relabel(label);
    int s1, s2, s3;
    uint64_t hsh = 0;
    if (ArithmEncoder ac{FreqTable{{1281, 1020, 836, 124, 4}}, outb, s1}; 1)
    for (auto x: sd) ac.write(x), hsh = hsh * 7 + x;
    if (ArithmEncoder ac{FreqTable{{2537, 393, 157, 139, 28, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1}}, outb, s2}; 1)
    for (auto x: hm) ac.write(x), hsh = hsh * 7 + x;
    out.wti(s1, 4);
    out.wti(s2, 4);
    out.wti(href.size(), 4);
    if (ArithmEncoder ac{CountingTable<int>(vector(sd.size(), 1), 1), outb, s3}; 1)
    for (auto x: href) ac.write(x), hsh = hsh * 7 + x;
    outb.wbflush();
    out.wti(s3, 4);
  }

  void rddoag() {
    int s1, s2, hrs, s3; in.rdi(s1, 4), in.rdi(s2, 4), in.rdi(hrs, 4), in.rdi(s3, 4);
    vector<int> sd(nc - contbit.size() * 3), hm(sd.size()), href(hrs, -1);
    uint64_t hsh = 0;
    if (ArithmDecoder ac{FreqTable{{1281, 1020, 836, 124, 4}}, inb, s1}; 1)
    for (auto& x: sd) x = ac.read(), hsh = hsh * 7 + x;
    if (ArithmDecoder ac{FreqTable{{2537, 393, 157, 139, 28, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1}}, inb, s2}; 1)
    for (auto& x: hm) x = ac.read(), hsh = hsh * 7 + x;
    if (ArithmDecoder ac{CountingTable<int>(vector(sd.size(), 1), 1), inb, s3}; 1)
    for (auto& x: href) x = ac.read(), hsh = hsh * 7 + x;
    inb.rbflush();
    vector<int> roots{};
    for (int i = sd.size(); i--; ) {
      to[i].resize(sd[i] + __builtin_popcount(hm[i]));
      for (int j = to[i].size(); j--; ) if (hm[i] & 1 << j) to[i][j] = href.back(), href.pop_back(); else to[i][j] = roots.back(), roots.pop_back();
      roots.push_back(i);
    }
  }

  void wtsoa() {
    wth(1);
    out.wti(conte.size(), pi);
    for (auto& [a, b]: conte) assert(max(a, b) < (1ll << 8 * pi));
    for (auto& [a, b]: conte) out.wti(a, pi), out.wti(b, pi);
    for (auto& s: contsz) out.wti(s, pi);
    for (auto x: contbit) outb.wtb(x);
    wtdoag();
    $i$ {
      out.wti(refd[i]), out.wti(bitd[i]);
      if (!spec[i] && bitd[i]) out.wti(data[i][0]);
    }
    vector<int> ord(nc);
    for (int i = 0; i < nc; ++i) ord[i] = i;
    stable_sort(ord.begin(), ord.end(), [&](int i, int j) { return tuple{refd[i], bitd[i], bitd[i]? data[i][0]: 0} < tuple{refd[j], bitd[j], bitd[j]? data[j][0]: 0}; });
    for (int lo: {0, 1})
    $i$ if (spec[i]) for (int j = spec[i] > 1? spec[i] - 2 << 1: lvl[i] * 2; j--; ) if (j % 2 == lo) out.wti(data[i].rbegin()[j]);
    $i$ if (spec[i] == 1) out.wti(data[i][1]);
    $po$ if (!spec[i] && bitd[i] % 2 && bitd[i] > 1) out.wti(brev8(data[i].back() ^ p)), p = data[i].back();
    $po$ if (!spec[i] && bitd[i] > 3) out.wti(data[i][1] ^ p), p = data[i][1];
    if (BitO tmp; 1) {
      $o$ if (!spec[i]) for (int j = min(2, bitd[i] / 2); j < bitd[i] / 2; ++j) tmp.wti(data[i][j]);
      multiwayencode(tmp.s, out, outb);
    }
    #define forh $i$ if (spec[i]) for (int t = spec[i] > 1? spec[i] - 2 << 1: lvl[i] * 2, j = 1 + (spec[i] == 1); j < bitd[i] / 2 - t; j += 32)
    forh for (int k = 0; k < 32; ++k) outb.wti(data[i][j + k]);
    outb.wti(outb.s.size() + 4, 4);
  }

  void rdsoa() {
    rdh(1);
    int sze; in.rdi(sze, pi);
    conte.resize(sze);
    contsz.resize(sze);
    for (auto& [a, b]: conte) in.rdi(a, pi), in.rdi(b, pi);
    for (auto& x: contsz) in.rdi(x, pi);
    contbit.resize(accumulate(contsz.begin(), contsz.end(), 0));
    for (auto& x: contbit) x = inb.rdb();
    rddoag();
    $i$ {
      in.rdi(refd[i]), in.rdi(bitd[i]), splitrefd(i);
      if (!spec[i] && bitd[i]) in.rdi(data[i][0]);
    }
    $i$ if (spec[i]) data[i][0] = spec[i];
    vector<int> ord(nc);
    for (int i = 0; i < nc; ++i) ord[i] = i;
    stable_sort(ord.begin(), ord.end(), [&](int i, int j) { return tuple{refd[i], bitd[i], bitd[i]? data[i][0]: 0} < tuple{refd[j], bitd[j], bitd[j]? data[j][0]: 0}; });
    for (int lo: {0, 1})
    $i$ if (spec[i]) for (int j = spec[i] > 1? spec[i] - 2 << 1: lvl[i] * 2; j--; ) if (j % 2 == lo) in.rdi(data[i].rbegin()[j]);
    $i$ if (spec[i] == 1) in.rdi(data[i][1]);
    $po$ if (!spec[i] && bitd[i] % 2 && bitd[i] > 1) in.rdi(data[i].back()), data[i].back() = p ^= brev8(data[i].back());
    $po$ if (!spec[i] && bitd[i] > 3) p = in.rdi(data[i][1]) ^= p;
    if (BitI tmp(multiwaydecode(in, inb)); 1) {
      $o$ if (!spec[i]) for (int j = min(2, bitd[i] / 2); j < bitd[i] / 2; ++j) tmp.rdi(data[i][j]);
    }
    forh for (int k = 0; k < 32; ++k) inb.rdi(data[i][j + k]);
  }
};

string compress(string s) {
  auto root = vm::std_boc_deserialize(s).move_as_ok();
  DAG dag;
  dag.in = {vm::std_boc_serialize(root, 0).move_as_ok().as_slice().str()};
  dag.rdaos();
  dag.contract();
  dag.wtsoa();
  return td::gzencode(dag.out.s, 1).as_slice().str() + dag.outb.s;
}

string decompress(string s) {
  int bin; BitI(s.substr(s.size() - 4)).rdi(bin, 4);
  DAG dag;
  dag.in = {td::gzdecode(s.substr(0, s.size() - bin)).as_slice().str()};
  dag.inb = {s.substr(s.size() - bin)};
  dag.rdsoa();
  dag.uncontract();
  dag.wtaos();
  auto root = vm::std_boc_deserialize(dag.out.s).move_as_ok();
  return vm::std_boc_serialize(root, 31).move_as_ok().as_slice().str();
}

int main(int argc, char* argv[]) {
  CHECK(argc == 2);
  string mode(argv[1]);
  CHECK(mode == "compress" || mode == "decompress");

  string base64_data;
  cin >> base64_data;
  CHECK(!base64_data.empty());

  string data(b64d(base64_data));

  if (mode == "compress") {
    data = compress(data);
  } else {
    data = decompress(data);
  }

  cout << td::base64_encode(data) << endl;
}
