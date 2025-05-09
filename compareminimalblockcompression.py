import base64
import os
import subprocess
import zlib, gzip, bz2, lzma
import brotli, paq, zstd, zstandard
from collections import defaultdict

def get_base64_size(s):
  try:
    decoded = base64.b64decode(s, validate=True)
  except binascii.Error:
    return None
  return len(decoded)

dr = 'scraping_2025-01-27T00-00-00_2025-02-03T00-00-00'
dr2 = 'minimal_2025-01-27T00-00-00_2025-02-03T00-00-00'
test_files = os.listdir(dr)

def check_subproc(s, file, text, timeout):
  result = subprocess.run([file, 'compress'], input=s, text=text, capture_output=True, timeout=timeout)
  assert result.returncode == 0
  if text:
    compressed_block = result.stdout.strip()
    compressed_size = get_base64_size(compressed_block)
  else:
    compressed_block = result.stdout
    compressed_size = len(compressed_block)
  result = subprocess.run([file, 'decompress'], input=compressed_block, text=text, capture_output=True, timeout=timeout)
  assert result.returncode == 0
  if text:
    assert result.stdout.strip() == s
  else:
    assert result.stdout == s
  return compressed_size

def check_final(s, s64):
  return check_subproc(s64, './final', True, 1.2)

def check_final_nodict(s, s64):
  return check_subproc(s64, './final_nodict', True, 1.2)

def check_zlib(s, s64):
  compressed = zlib.compress(s, 9)
  assert zlib.decompress(compressed) == s
  return len(compressed)

def check_gzip(s, s64):
  compressed = gzip.compress(s, 9)
  assert gzip.decompress(compressed) == s
  return len(compressed)

def check_bz2(s, s64):
  compressed = bz2.compress(s, 9)
  assert bz2.decompress(compressed) == s
  return len(compressed)

def check_lzma(s, s64):
  compressed = lzma.compress(s)
  assert lzma.decompress(compressed) == s
  return len(compressed)

def check_brotli(s, s64):
  compressed = brotli.compress(s, lgwin=24, lgblock=24)
  assert brotli.decompress(compressed) == s
  return len(compressed)

def check_paq(s, s64):
  compressed = paq.compress(s)
  assert paq.decompress(compressed) == s
  return len(compressed)

def check_zstd(s, s64):
  compressed = zstd.compress(s, 22)
  assert zstd.decompress(compressed) == s
  return len(compressed)

def check_zstandard(s, s64):
  compressed = zstandard.compress(s, 22)
  assert zstandard.decompress(compressed) == s
  return len(compressed)

def check_Zstandard(s, s64):
  return check_subproc(s, '../zstd/wrapper', False, 2)

def check_zopfli(s, s64):
  result = subprocess.run(['../zopfli/wrapper', 'compress'], input=s, text=False, capture_output=True, timeout=2)
  assert result.returncode == 0
  compressed_size = len(result.stdout)
  assert zlib.decompress(result.stdout) == s
  return compressed_size

def check_zpaq(s, s64):
  return check_subproc(s, '../zpaq/wrapper', False, 2)

results = defaultdict(lambda: [])

for test_file in test_files:
  print(test_file)
  with open(dr + '/' + test_file, "r") as f:
    original_block = f.read().strip()
  with open(dr2 + '/' + test_file, "r") as f:
    minimal_block = f.read().strip()
  original_size = get_base64_size(original_block)
  minimal_size = get_base64_size(minimal_block)
  decoded = base64.b64decode(original_block, validate=True)
  decoded2 = base64.b64decode(minimal_block, validate=True)
  assert original_size is not None
  assert original_size <= 2 ** 21
  assert minimal_size is not None
  assert minimal_size <= 2 ** 21
  
  lst = "final final_nodict zlib gzip bz2 lzma brotli paq zstd zstandard Zstandard zopfli zpaq".split()
  results["orig"].append(len(decoded2))
  for s in lst:
    f = eval("check_" + s)
    if s.startswith("final"):
      res = f(decoded, original_block)
    else:
      res = f(decoded2, minimal_block)
    results[s].append(res)

for k in results.keys():
  n = len(results[k])
  m = 0
  tsk = 0
  tso = 0
  for i in range(n):
    m += 2 * results['orig'][i] / (results['orig'][i] + results[k][i])
    tsk += results[k][i]
    tso += results['orig'][i]
  print(k, "%.6f" % (m / n), "%.6f" % (tsk / tso))