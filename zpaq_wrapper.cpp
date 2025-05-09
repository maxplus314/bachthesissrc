#include "libzpaq.h"
#include <iostream>

void libzpaq::error(const char* msg) {  // print message and exit
  fprintf(stderr, "Oops: %s\n", msg);
  exit(1);
}

class In: public libzpaq::Reader {
public:
  int get() {return std::cin.get();}  // returns byte 0..255 or -1 at EOF
} in;

class Out: public libzpaq::Writer {
public:
  void put(int c) { std::cout.put(c); }  // writes 1 byte 0..255
} out;

int main(int argc, char* argv[]) {
  using namespace std;
  
  string mode(argv[1]);
  if (mode == "compress") {
    libzpaq::compress(&in, &out, "5");
  } else {
    libzpaq::decompress(&in, &out);
  }
}