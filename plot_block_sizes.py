import argparse
import os
from matplotlib import pyplot as plt

parser = argparse.ArgumentParser()
parser.add_argument('--testdir', default='scraping_2025-01-20T00-00-00_2025-01-27T00-00-00', type=str, help='directory with base64-encoded .txt block files')
args = parser.parse_args()
test_files = os.listdir(args.testdir)
assert test_files

fig, ax = plt.subplots()
# ax.set_title('Кумулята эмпирической функции распределения\nразмеров блоков')
ax.set_ylabel('Размер, КиБ')
ax.set_xlabel('Номер блока')
for item in ([ax.title, ax.xaxis.label, ax.yaxis.label] +
             ax.get_xticklabels() + ax.get_yticklabels()):
  item.set_fontsize(20)
ax.plot(sorted(len(open(args.testdir + '/' + f).read()) * 6 / 2**13 for f in test_files))
plt.show()