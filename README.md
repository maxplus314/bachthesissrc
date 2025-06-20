Пример компиляции и запуска результата разработки:

```console
$ ./compile.sh final.cpp
$ ./executable.sh compress <block.base64 >compressed.base64
$ ./executable.sh decompress <compressed.base64 >decompressed.base64
$ diff block.base64 decompressed.base64 -wqs
```

[Ссылка](https://codeforces.com/contest/2054/problem-materials/problem-a-ton-compress-contest-linux.zip) для загрузки использованной части TON Blockchain Library.