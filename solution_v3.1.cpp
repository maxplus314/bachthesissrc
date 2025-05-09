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

vector<int> numways{2, 3, 4, 5};
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
  if (bits.size() > 9 << 18) numways.pop_back();
  if (bits.size() > 12 << 18) numways.pop_back();
  if (bits.size() > 13 << 18) numways.pop_back();
  const int lmax = 1 << 10, pi = 8, pd = 32 - __builtin_clz(bits.size() - 1) - 4, pl = 10, pt = 0;
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
  if (ArithmEncoder ac{CountingTable<int64_t>(vector<int64_t>(numways.size(), 1), 1), outb, acbits}; 1)
  for (auto& [l, v]: ops) ac.write(find(numways.begin(), numways.end(), v.size()) - numways.begin());
  out.wti(acbits, 4);
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
    ac.f = SubsetTable(p + 1, (ssz + ops.size() - i++) / 2);
    ac.write(v[0]);
    ssz -= v.size();
    p = v[0];
  }
  out.wti(acbits, 4);
  vector<int64_t> prior(bits.size()), cnt(bits.size());
  for (int i = 0; i < bits.size(); ++i) prior[i] = multiway_delta_prior(i, bits.size());
  if (ArithmEncoder ac{CountingTable<int64_t>(prior, 0), outb, acbits}; 1)
  for (auto [l, v]: ops)
  for (int i = 0; ++i < v.size(); ) {
    int d = v[i - 1] - v[i];
    ac.write(d);
    ++cnt[d];
    ac.f.upd(d, prior[d] * (cnt[d] < 4? 8: 1));
  }
  out.wti(acbits, 4);
  vector<int> minx(bits.size(), bits.size());
  for (int i = bits.size(); i--; ) minx[dsu.getppc(i) / 2] = i;
  sort(minx.begin(), minx.end());
  for (auto x: minx) if (x < bits.size()) outb.wtb(bits[x]);
  cerr << bits.size() << ' ' << ops.size() << '\n';
}

string multiwaydecode(BitI& in, BitI& inb) {
  // int sz; in.rdi(sz, 4);
  // string res(sz, '\0');
  // for (auto& c: res) in.rdi(c);
  // return res;
  int nbits, nops;
  in.rdi(nbits, 4), in.rdi(nops, 4);
  if (nbits > 9 << 18) numways.pop_back();
  if (nbits > 12 << 18) numways.pop_back();
  if (nbits > 13 << 18) numways.pop_back();
  cerr << nbits << ' ' << nops << '\n';
  vector<pair<int, vector<int>>> ops(nops);
  int ssz = 0, acbits;
  in.rdi(acbits, 4);
  if (ArithmDecoder ac{CountingTable<int64_t>(vector<int64_t>(numways.size(), 1), 1), inb, acbits}; 1)
  for (auto& [l, v]: ops) v.resize(numways[ac.read()]);
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
    ac.f = SubsetTable(p + 1, (ssz + ops.size() - i++) / 2);
    v[0] = ac.read();
    ssz -= v.size();
    p = v[0];
  }
  vector<int64_t> prior(nbits), cnt(nbits);
  for (int i = 0; i < nbits; ++i) prior[i] = multiway_delta_prior(i, nbits);
  in.rdi(acbits, 4);
  if (ArithmDecoder ac{CountingTable<int64_t>(prior, 0), inb, acbits}; 1)
  for (auto& [l, v]: ops)
  for (int i = 0; ++i < v.size(); ) {
    int d = ac.read();
    v[i] = v[i - 1] - d;
    ++cnt[d];
    ac.f.upd(d, prior[d] * (cnt[d] < 4? 8: 1));
  }
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
  return s;
}

string allc = b64d("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");
vector<string> allcsp;
map<string, int> c2i;
string allh = b64d("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");
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
      if (A.size() < 1) continue; // < 2 still fails one online test, < 1 -- two
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
      // auto r = roots[0]; roots.erase(roots.begin()); // wtf?
      auto r = roots.back(); roots.pop_back(); // wtf?
      label[r] = i;
      sd.push_back(0);
      hm.push_back(0);
      for (int j = -1; auto x: to[r]) if (++j, --remref[x]) href.push_back(x), hm[i] |= 1 << j; else roots.push_back(x), ++sd[i];
    }
    for (auto& x: href) x = label[x];
    relabel(label);
    int s1, s2, s3;
    uint64_t hsh = 0;
    // if (auto ac = ArithmEncoder{FreqTable{{3689, 933, 1, 505, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2013, 629, 617, 53, 1, 9, 29, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3945, 13, 13, 1, 113, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 489, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,}}, outb, s1}; 1)
    // for (int i = 0; i < sd.size(); ++i) ac.write(sd[i] * 16 + hm[i]);
    if (ArithmEncoder ac{FreqTable{{1281, 1020, 836, 124, 4}}, outb, s1}; 1)
    for (auto x: sd) ac.write(x), hsh = hsh * 7 + x;
    if (ArithmEncoder ac{FreqTable{{2537, 393, 157, 139, 28, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1}}, outb, s2}; 1)
    for (auto x: hm) ac.write(x), hsh = hsh * 7 + x;
    cerr << "hsh " << hsh << '\n';
    out.wti(s1, 4);
    out.wti(s2, 4);
    cerr << href.size() << '\n';
    vector<int> pos, inlis;
    cerr << lis(href, less{}).size() << ' ' << lis(href, less_equal{}).size() << '\n';
    cerr << lis(href, greater{}).size() << ' ' << lis(href, greater_equal{}).size() << '\n';
    cerr << lis(href, less{}, 1).size() << ' ' << lis(href, less{}, 2).size() << ' ' << lis(href, less{}, 3).size() << ' ' << lis(href, less{}, 4).size() << '\n';
    cerr << lis(href, less{}, -1).size() << ' ' << lis(href, less{}, -2).size() << ' ' << lis(href, less{}, -3).size() << ' ' << lis(href, less{}, -4).size() << '\n';
    pos = lis(href, less{}, -2);
    tie(inlis, href) = unmerge(href, pos); 
    for (int d = 0; auto& x: inlis) x += d, d += 2;
    // for (auto& x: inlis) cerr << x << ' ', hsh = hsh * 7 + x; cerr << '\n';
    cerr << "hsh " << hsh << '\n';
    // for (auto& x: pos) cerr << x << ' '; cerr << '\n';
    out.wti(inlis.size(), 4);
    out.wti(href.size(), 4);
    subsetencode(sd.size() + inlis.size() * 2, {inlis.begin(), inlis.end()}, out, outb, 0, 0);
    // cerr << href.size() + inlis.size() << '\n';
    subsetencode(href.size() + inlis.size(), {pos.begin(), pos.end()}, out, outb, 0, 0);
    vector<int64_t> freq(sd.size());
    for (auto& v: freq) v = 1e6;
    if (ArithmEncoder ac{CountingTable<int64_t>(freq, 3e6), outb, s3}; 1)
    for (auto x: href) ac.write(x), hsh = hsh * 7 + x;
    cerr << "hsh " << hsh << '\n';
    out.wti(s3, 4);
    // map<int, int> cnt;
    // for (auto& v: href) cerr << v << ' '; cerr << '\n';
    // for (int p = 0; auto& v: href) cerr << v - p << ' ', p = v; cerr << '\n';
    // for (auto x: href) ++cnt[x];
    // for (auto& [k, v]: cnt) cerr << v << ' '; cerr << '\n';
    // cerr << lis(href, less{}).size() << ' ' << lis(href, less_equal{}).size() << '\n';
    // cerr << lis(href, greater{}).size() << ' ' << lis(href, greater_equal{}).size() << '\n';
    // href = unmerge(href, lis(href, less{})).second;
    // cerr << lis(href, less{}).size() << ' ' << lis(href, less_equal{}).size() << '\n';
    // cerr << lis(href, greater{}).size() << ' ' << lis(href, greater_equal{}).size() << '\n';
    // href = unmerge(href, lis(href, less{})).second;
    // cerr << lis(href, less{}).size() << ' ' << lis(href, less_equal{}).size() << '\n';
    // cerr << lis(href, greater{}).size() << ' ' << lis(href, greater_equal{}).size() << '\n';
    // href = unmerge(href, lis(href, less{})).second;
    // cerr << lis(href, less{}).size() << ' ' << lis(href, less_equal{}).size() << '\n';
    // cerr << lis(href, greater{}).size() << ' ' << lis(href, greater_equal{}).size() << '\n';
    // href = unmerge(href, lis(href, less{})).second;
    // for (auto x: href) outb.wtbi(x, pr), hsh = hsh * 7 + x;
    // cerr << href[0] << '\n';
    // cerr << hsh << '\n';
    // cerr << sd.size() << '\n';
    cerr << s1 << ' ' << s2 << ' ' << href.size() << ' ' << s3 << '\n';
  }

  void rddoag() {
    int s1, s2, inlissz, hrs, s3; in.rdi(s1, 4), in.rdi(s2, 4), in.rdi(inlissz, 4), in.rdi(hrs, 4);
    vector<int> sd(nc - contbit.size() * 3), hm(sd.size()), href(inlissz + hrs, -1);
    uint64_t hsh = 0;
    // if (auto ac = ArithmDecoder{FreqTable{{3689, 933, 1, 505, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2013, 629, 617, 53, 1, 9, 29, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3945, 13, 13, 1, 113, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 489, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,}}, inb, s1}; 1)
    // for (int i = 0; i < sd.size(); ++i) { auto t = ac.read(); sd[i] = t / 16, hm[i] = t % 16; }
    if (ArithmDecoder ac{FreqTable{{1281, 1020, 836, 124, 4}}, inb, s1}; 1)
    for (auto& x: sd) x = ac.read(), hsh = hsh * 7 + x;
    if (ArithmDecoder ac{FreqTable{{2537, 393, 157, 139, 28, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1}}, inb, s2}; 1)
    for (auto& x: hm) x = ac.read(), hsh = hsh * 7 + x;
    cerr << "hsh " << hsh << '\n';
    auto inlis = subsetdecode(sd.size() + inlissz * 2, inlissz, in, inb, 0, 0);
    for (int d = 0; auto& x: inlis) x -= d, d += 2;
    cerr << href.size() << '\n';
    auto pos = subsetdecode(href.size(), inlissz, in, inb, 0, 0);
    for (int i = 0; i < inlissz; ++i) href[pos[i]] = inlis[i], hsh = hsh * 7 + inlis[i];
    cerr << "hsh " << hsh << '\n';
    // for (int i = 0; i < inlissz; ++i) cerr << pos[i] << ' '; cerr << '\n';
    in.rdi(s3, 4);
    cerr << s3 << '\n';
    vector<int64_t> freq(sd.size());
    for (auto& v: freq) v = 1e6;
    if (ArithmDecoder ac{CountingTable<int64_t>(freq, 3e6), inb, s3}; 1)
    for (auto& x: href) if (!~x) x = ac.read(), hsh = hsh * 7 + x;
    cerr << "hsh " << hsh << '\n';
    // for (auto& x: href) inb.rdbi(x, pr), hsh = hsh * 7 + x;
    vector<int> roots{};
    for (int i = sd.size(); i--; ) {
      to[i].resize(sd[i] + __builtin_popcount(hm[i]));
      for (int j = to[i].size(); j--; ) if (hm[i] & 1 << j) to[i][j] = href.back(), href.pop_back(); else to[i][j] = roots.back(), roots.pop_back();
      roots.push_back(i);
    }
  }

  void wtsoa() {
    wth(1);
    $i$ out.wti(refd[i]), out.wti(bitd[i]);
    $i$ for (auto& j: to[i]) out.wti(j, pi);
    $i$ for (int j = 0; j * 2 < bitd[i]; ++j) out.wti(data[i][j]);
  }

  void rdsoa() {
    rdh(1);
    $i$ in.rdi(refd[i]), in.rdi(bitd[i]), splitrefd(i);
    $i$ for (auto& j: to[i] = vector<int>(nref[i])) in.rdi(j, pi);
    $i$ for (int j = 0; j * 2 < bitd[i]; ++j) in.rdi(data[i][j]);
  }
};

string compress(string s) {
  auto root = vm::std_boc_deserialize(s).move_as_ok();
  DAG dag;
  dag.in = {vm::std_boc_serialize(root, 0).move_as_ok().as_slice().str()};
  dag.rdaos();
  dag.wtsoa();
  return td::gzencode(dag.out.s, 1).as_slice().str();
}

string decompress(string s) {
  DAG dag;
  dag.in = {td::gzdecode(s).as_slice().str()};
  dag.rdsoa();
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
