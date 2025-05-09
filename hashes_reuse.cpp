#include <algorithm>
#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_map>
#include "td/utils/base64.h"

using namespace std;

int main() {
  ifstream ifs("hashes", ios::binary);
  unordered_map<string, int> cnt;
  char buf[33]{};
  while (ifs.read(buf, 32)) ++cnt[string(buf, buf + 32)];
  vector<pair<int, string>> occ;
  for (auto& [k, v]: cnt) occ.push_back({v, k});
  sort(occ.rbegin(), occ.rend());
  occ.resize(min(occ.size(), {1000}));
  // for (auto& [v, k]: occ) cout << v << ' ';
  ofstream ofs("tophashes", ios::binary);
  for (auto& [v, k]: occ) ofs.write(&k[0], 32);
  occ.resize(min(occ.size(), {440}));
  string t;
  for (auto& [v, k]: occ) t += k;
  cout << td::base64_encode(t) << '\n';
}