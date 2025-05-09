import os
import sys
import requests
import base64
import random
import time
import multiprocessing
import argparse
import datetime

def search(seqno, fout):
  view = ""
  while 1:
    try:
      blocks = []
      resp = requests.get(f'http://explorer.toncenter.com/search?workchain=-1&shard=8000000000000000&seqno={seqno}', timeout=10)
      resp.close()
      assert resp.status_code == 200, "fail search response " + str(resp)
      view = resp.text
      ts = int(view.split('<tr><th>time</th><td>')[1].split(' ')[0])
      roothash = filehash = ""
      for x in view.split('name="roothash" value=')[1:]:
        t = x.split('"')[1]
        if t:
          if roothash:
            assert roothash == t, "ambiguous roothash"
          else:
            roothash = t
      for x in view.split('name="filehash" value=')[1:]:
        t = x.split('"')[1]
        if t:
          if filehash:
            assert filehash == t, "ambiguous filehash"
          else:
            filehash = t
      assert roothash, "empty roothash"
      assert filehash, "empty filehash"
      blocks += [["-1", "8000000000000000", str(seqno), roothash, filehash]]
      shards = view.split(')</td><td><a href="/block?')[1:]
      assert shards, "no shards"
      for shard in shards:
        cur = [shard.split('"')[0]]
        amp = ''
        for name in ["workchain", "shard", "seqno", "roothash", "filehash"]:
          pref = amp + name + '='
          t = cur[-1].split(pref)
          assert len(t) == 2, f"failed split pref {pref} {len(t)}"
          cur = cur[:-1] + t
          amp = '&'
        blocks += [cur[1:]]
      break
    except Exception as e:
      # print(view, file=fout)
      print(type(e), e, file=fout)
      print("retry search", file=fout)
      time.sleep(random.random() * 5)
  return ts, blocks

def download(workchain, shard, seqno, roothash, filehash, fout):
  data = ''
  while 1:
    try:
      resp = requests.get(f'http://explorer.toncenter.com/download?workchain={workchain}&shard={shard}&seqno={seqno}&roothash={roothash}&filehash={filehash}', timeout=10)
      resp.close()
      assert resp.status_code == 200, "fail download response " + str(resp)
      data = resp.content
      assert data, "empty download content"
      assert data[:4] == b'\xb5\xee\x9cr', "wrong download header"
      break
    except Exception as e:
      print(type(e), e, file=fout)
      print("retry download", file=fout)
      time.sleep(random.random() * 5)
  return data

if __name__ == "__main__":
  parser = argparse.ArgumentParser(description="scrape blocks")
  parser.add_argument('from_datetime', type=datetime.datetime.fromisoformat, help='constructs minimum block datetime from ISO format')
  parser.add_argument('till_datetime', type=datetime.datetime.fromisoformat, help='constructs maximum block datetime from ISO format')
  parser.add_argument('num_blocks', type=int, help='number of blocks to scrape')
  parser.add_argument('num_proc', type=int, default=8, nargs='?', help='number of subprocesses to use')
  args = parser.parse_args()
  tlo = args.from_datetime.timestamp()
  thi = args.till_datetime.timestamp()
  dr = f"scraping_{args.from_datetime.isoformat().replace(':', '-')}_{args.till_datetime.isoformat().replace(':', '-')}/"
  os.makedirs(dr)
  os.makedirs('tmp', exist_ok=True)

  def fun(i, cnt):
    with open(f"tmp/scrapinglog{i}", "w", 1) as fout:
      lo = 0
      hi = 47427770
      while cnt.value > 0:
        mseqno = random.randint(lo, hi - 1)
        ts, shards = search(mseqno, fout)
        if ts < tlo:
          lo = mseqno + 1
          continue
        if ts >= thi:
          hi = mseqno
          continue
        for workchain, shard, seqno, roothash, filehash in shards:
          print(f"{workchain}_{shard}_{seqno.rjust(8, '0')}_{roothash}_{filehash}", file=fout)
          data = download(workchain, shard, seqno, roothash, filehash, fout)
          with cnt.get_lock():
            if cnt.value <= 0: break
            cnt.value -= 1
          with open(f"{dr}/{str(mseqno).rjust(8, '0')}_{workchain}_{shard.rstrip('0')}_{seqno.rjust(8, '0')}.txt", 'w') as block:
            block.write(base64.b64encode(data).decode())

  procs = []
  cnt = multiprocessing.Value('i', args.num_blocks)
  for i in range(args.num_proc):
    proc = multiprocessing.Process(target=fun, args=(i, cnt))
    proc.start()
    procs.append(proc)

  for proc in procs:
    proc.join()