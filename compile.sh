set -xe
TBM=ton_blockchain_ton_mini
g++ -O2 -std=c++2a -I $TBM -I $TBM/crypto -I $TBM/tdutils -I $TBM/ton -I $TBM/common "$1" -L$TBM -lton_crypto_lib -o executable
