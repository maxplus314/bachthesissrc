#include "zstd.h"
#include <iostream>
#include <cassert>

int main(int argc, char* argv[]) {
  using namespace std;

  string mode(argv[1]);
  string inp(1 << 28, '\0');
  cin.read(&inp[0], inp.size());
  assert(cin.eof());
  inp.resize(cin.gcount());
  string out(1 << 28, '\0');
  if (mode == "compress") {
    auto t = ZSTD_compress(&out[0], out.size(), &inp[0], inp.size(), ZSTD_maxCLevel());
    assert(!ZSTD_isError(t) && t < out.size());
    cout.write(&out[0], t);
  } else {
    auto t = ZSTD_decompress(&out[0], out.size(), &inp[0], inp.size());
    assert(!ZSTD_isError(t) && t < out.size());
    cout.write(&out[0], t);
  }
}