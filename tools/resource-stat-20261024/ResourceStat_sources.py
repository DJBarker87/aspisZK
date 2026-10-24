"""Fetch primary references for hash receipts. No GPL code is saved."""
import datetime
import hashlib
import json
from pathlib import Path
import urllib.request

HERE=Path(__file__).resolve().parent
OUT=HERE.parents[1]/'evidence/resource-stat-20261024'

def main():
    expected=json.loads((OUT/'primary-source-hashes.json').read_text())
    urls=[r['url'] for r in expected]+[
        'https://docs.kernel.org/6.8/admin-guide/cgroup-v2.html',
        'https://raw.githubusercontent.com/torvalds/linux/v6.8/mm/memcontrol.c',
        'https://raw.githubusercontent.com/torvalds/linux/v6.8/include/linux/mm_inline.h']
    results=[]
    for url in urls:
        with urllib.request.urlopen(url,timeout=30) as response:
            data=response.read(2_000_000)
            assert not response.read(1),'oversized reference'
            digest=hashlib.sha256(data).hexdigest()
            previous=next((r for r in expected if r['url']==url),None)
            if previous:assert digest==previous['sha256'] and len(data)==previous['size']
            results.append(dict(url=url,response_url=response.url,status=response.status,
                sha256=digest,size=len(data),etag=response.headers.get('ETag'),
                last_modified=response.headers.get('Last-Modified'),
                observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
    (OUT/'primary-fetch.json').write_text(json.dumps(dict(references=results,
        code_copied=False,assessment='reference retrieval, not live-kernel source identity gate'),indent=2)+'\n')
    print(json.dumps(dict(result='PASS',references=len(results))))

if __name__=='__main__':main()
