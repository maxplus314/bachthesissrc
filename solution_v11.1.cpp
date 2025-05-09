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
void multiwayencode(string s, BitO& out, BitO& outb, vector<array<int, 2>> known) {
  // int sz = s.size();
  // out.wti(sz, 4);
  // for (auto c: s) out.wti(c);
  // return;
  string bits, bits2;
  for (auto c: s) for (int k = 8; k--; ) bits += char(c >> k & 1);
  cerr << bits.size() << '\n';
  SA sa(bits);
  DSU dsu(bits.size());
  {
    int z = -1, o = -1;
    for (auto& [l, r]: known)
    for(int i = l * 8; i < r * 8; ++i) {
      auto& t = bits[i]? z: o;
      if (~t) dsu.uni(i, t, 0);
      else t = i;
    }
  }
  // if (bits.size() > 9 << 18) numways.pop_back();
  // if (bits.size() > 12 << 18) numways.pop_back();
  // if (bits.size() > 13 << 18) numways.pop_back();
  const int lmax = 1 << 10, pi = 8, pd = 32 - __builtin_clz(bits.size() - 1) - 4, pl = 10, pt = 0;
  // const int lmax = 1 << 10, pi = 32 - __builtin_clz(bits.size() - 1), pd = pi, pl = 10, pt = 0;
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
  outb.wbflush();
  cerr << bits.size() << ' ' << ops.size() << '\n';
}

string multiwaydecode(string s, BitI& in, BitI& inb, vector<array<int, 2>> known) {
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
  {
    int z = -1, o = -1;
    string bits;
    for (auto c: s)
    for (int k = 8; k--; ) bits += char(c >> k & 1);
    for (auto& [l, r]: known)
    for(int i = l * 8; i < r * 8; ++i) {
      auto& t = bits[i]? z: o;
      if (~t) dsu.uni(i, t, 0);
      else t = i;
    }
  }
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
  s = string(bits.size() / 8, '\0');
  for (int i = 0; auto& c: s) for (int k = 8; k--; ) c |= bits[i++] << k;
  inb.rbflush();
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
    vector<char> knc(nc);
    if (c2i.size()) {
      vector<int64_t> cms0, cms1;
      $i$ if (auto it = c2i.find(string{(char)refd[i], (char)bitd[i]} + string(data[i].begin(), data[i].end())); it != c2i.end()) cms0.push_back(i), cms1.push_back(it->second), c2i.erase(it), knc[i] = 1;
      out.wti(cms0.size(), 4);
      for (auto x: cms0) outb.wtbi(x, 32 - __builtin_clz(nc - 1 | 1));
      for (auto x: cms1) outb.wtbi(x, 32 - __builtin_clz(allcsp.size() - 1 | 1));
    }
    $i$ if (!knc[i]) {
      out.wti(refd[i]), out.wti(bitd[i]);
      if (!spec[i] && bitd[i]) out.wti(data[i][0]);
    }
    vector<int> ord(nc);
    for (int i = 0; i < nc; ++i) ord[i] = i;
    stable_sort(ord.begin(), ord.end(), [&](int i, int j) { return tuple{refd[i], bitd[i], bitd[i]? data[i][0]: 0} < tuple{refd[j], bitd[j], bitd[j]? data[j][0]: 0}; });
    for (int lo: {0, 1})
    $i$ if (spec[i]) for (int j = spec[i] > 1? spec[i] - 2 << 1: lvl[i] * 2; j--; ) if (j % 2 == lo) out.wti(data[i].rbegin()[j]);
    $i$ if (spec[i] == 1) out.wti(data[i][1]);
    $po$ if (!spec[i] && bitd[i] % 2 && bitd[i] > 1 && !knc[i]) out.wti(brev8(data[i].back() ^ p)), p = data[i].back();
    $po$ if (!spec[i] && bitd[i] > 3 && !knc[i]) out.wti(data[i][1] ^ p), p = data[i][1];
    if (BitO tmp; 1) {
      vector<array<int, 2>> known;
      $o$ if (!spec[i]) {
        int t = tmp.s.size();
        for (int j = min(2, bitd[i] / 2); j < bitd[i] / 2; ++j) tmp.wti(data[i][j]);
        if (knc[i]) known.push_back({t, (int)tmp.s.size()});
      }
      multiwayencode(tmp.s, out, outb, known);
    }
    int pos = 0;
    #define forh $i$ if (spec[i]) for (int t = spec[i] > 1? spec[i] - 2 << 1: lvl[i] * 2, j = 1 + (spec[i] == 1); j < bitd[i] / 2 - t; j += 32, ++pos)
    forh ;
    int phi = 32 - __builtin_clz(h2i.size() - 1 | 1), php = 32 - __builtin_clz(pos - 1 | 1);
    vector<char> known(pos);
    pos = 0;
    forh if (auto it = h2i.find({&data[i][j], &data[i][j] + 32}); it != h2i.end()) {
      outb.wtb(1);
      outb.wtbi(it->second, phi);
      outb.wtbi(pos, php);
      known[pos] = 1;
    }
    pos = 0;
    outb.wtb(0);
    outb.wbflush();
    forh if (!known[pos]) for (int k = 0; k < 32; ++k) outb.wti(data[i][j + k]);
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
    vector<char> knc(nc);
    if (c2i.size()) {
      int kcc; in.rdi(kcc, 4);
      vector<int> cms0(kcc), cms1(kcc);
      for (auto& x: cms0) inb.rdbi(x, 32 - __builtin_clz(nc - 1 | 1));
      for (auto& x: cms1) inb.rdbi(x, 32 - __builtin_clz(allcsp.size() - 1 | 1));
      for (int i = 0; i < kcc; ++i) {
        int j = cms0[i];
        knc[j] = 1;
        string t = allcsp[cms1[i]];
        refd[j] = t[0];
        bitd[j] = (uint8_t)t[1];
        data[j].resize((uint8_t)t[1] + 1 >> 1);
        splitrefd(j);
        copy(t.begin() + 2, t.end(), data[j].begin());
      }  
    }
    $i$ if (!knc[i]) {
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
    $po$ if (!spec[i] && bitd[i] % 2 && bitd[i] > 1 && !knc[i]) in.rdi(data[i].back()), data[i].back() = p ^= brev8(data[i].back());
    $po$ if (!spec[i] && bitd[i] > 3 && !knc[i]) p = in.rdi(data[i][1]) ^= p;
    {
      vector<array<int, 2>> known;
      string t;
      $o$ if (!spec[i]) {
        int f = t.size();
        for (int j = min(2, bitd[i] / 2); j < bitd[i] / 2; ++j) t += data[i][j];
        if (knc[i]) known.push_back({f, (int)t.size()});
      }
      if (BitI tmp(multiwaydecode(t, in, inb, known)); 1) {
        $o$ if (!spec[i]) for (int j = min(2, bitd[i] / 2); j < bitd[i] / 2; ++j) tmp.rdi(data[i][j]);
      }
    }
    int pos = 0;
    forh ;
    int phi = 32 - __builtin_clz(h2i.size() - 1 | 1), php = 32 - __builtin_clz(pos - 1 | 1);
    vector<int> known(pos, -1);
    pos = 0;
    while (inb.rdb()) {
      int i, p;
      inb.rdbi(i, phi);
      inb.rdbi(p, php);
      known[p] = i;
    }
    inb.rbflush();
    forh if (~known[pos]) copy_n(&allh[known[pos] * 32], 32, &data[i][j]); else for (int k = 0; k < 32; ++k) inb.rdi(data[i][j + k]);
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
  allc = td::gzdecode(allc).as_slice().str();
  for (int i = 0, j = 0; i < allc.size(); ) {
    int l = ((uint8_t)allc[i + 1] + 5) / 2;
    allcsp.push_back(allc.substr(i, l));
    c2i[allc.substr(i, l)] = j++;
    i += l;
  }
  for (int i = 0; i < allh.size() / 32; ++i) h2i[allh.substr(i * 32, 32)] = i;
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
