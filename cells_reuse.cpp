#include <bits/stdc++.h>
#include "td/utils/Gzip.h"
#include "td/utils/base64.h"

using namespace std;

auto byfreq = [](auto& m) {
  using K = decay_t<decltype(m.begin()->first)>;
  using V = decay_t<decltype(m.begin()->second)>;
  vector<pair<V, K>> res;
  for (auto& [k, v]: m) res.push_back({v, k});
  sort(res.rbegin(), res.rend());
  return res;
};

auto getmaxfreq = [](auto& v) {
  using K = decay_t<decltype(v[0])>;
  using V = int;
  unordered_map<K, V> m;
  for (auto& v: v) ++m[v];
  V res = 0;
  for (auto& [k, v]: m) res = max(res, v);
  return res;
};

using CS = tuple<int, int, size_t>;

namespace std { template<> struct hash<CS>: hash<size_t> { size_t operator()(const CS& a) const { return get<2>(a); } }; }

unordered_map<CS, double> weight;
unordered_map<CS, double> prio;
unordered_map<CS, int> rnk;
unordered_map<size_t, string> tch2s;

CS cs(string s) { return {s.size(), max(0, {s.size() * 2 - getmaxfreq(s) * 2 - 5}), std::hash<string>{}(s)}; }

struct Block {
  bool not_master;
  int sz;
  vector<CS> c;
};

int main() {
  auto rdblock = [](auto& in) -> Block {
    int sz, ndc; in.read((char*)&sz, 4), in.read((char*)&ndc, 4);
    if (in.eof()) return {0, -1};
    Block b{0, sz};
    for (int i = 0; i < ndc; ++i) {
      uint8_t refd, bitd; in.read((char*)&refd, 1), in.read((char*)&bitd, 1);
      string s(bitd + 1 >> 1, '\0');
      in.read(&s[0], s.size());
      s = string{refd, bitd} + s;
      auto c = cs(s);
      tch2s[get<2>(c)] = s;
      b.c.push_back(c);
    }
    assert(!in.eof());
    return b;
  };
  auto rdblocks = [&](vector<const char*> files) -> vector<Block> {
    vector<Block> res;
    for (auto s: files) if (ifstream in(s, ios::binary); 1)
    while (1) {
      auto b = rdblock(in);
      if (!~b.sz) break;
      else res.push_back(b);
    }
    return res;
  };
  vector<Block> sb = rdblocks({"cells"});
  for (auto& b: sb) {
    unordered_map<CS, int> cnt;
    for (auto& c: b.c) ++cnt[c];
    for (auto& [c, n]: cnt) if (n == 1) prio[c] += get<1>(c) * .5 / get<0>(c) / b.sz;
  }
  auto bfp = byfreq(prio);
  // bfp.resize(1e3);
  // for (auto& [v, k]: bfp) cout << v / 2 << ' ';
  string t;
  for (auto& [v, k]: bfp) if (t.size() + tch2s[get<2>(k)].size() < 28270) t += tch2s[get<2>(k)];
  cout << td::base64_encode(td::gzencode(t, 2)) << '\n';
}