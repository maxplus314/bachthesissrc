#include "src/zopfli/zopfli.h"
#include <iostream>
#include <cassert>

int main(int argc, char* argv[]) {
  using namespace std;

  string mode(argv[1]);
  string inp(1 << 28, '\0');
  cin.read(&inp[0], inp.size());
  assert(cin.eof());
  inp.resize(cin.gcount());
  if (mode == "compress") {
    ZopfliOptions options;
    ZopfliInitOptions(&options);
    options.numiterations = 15;
    unsigned char* out;
    size_t outsize{};
    ZopfliCompress(&options, ZOPFLI_FORMAT_ZLIB, (unsigned char*)&inp[0], inp.size(), &out, &outsize);
    cout.write((char*)out, outsize);
  } else {
    return -1;
  }
}
