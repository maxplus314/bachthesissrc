set -xe
suf=2025-01-27T00-00-00_2025-02-03T00-00-00
ls scraping_$suf | xargs -I{} -n1 bash -c "./executable_ compress <scraping_$suf/{} >minimal_$suf/{}"