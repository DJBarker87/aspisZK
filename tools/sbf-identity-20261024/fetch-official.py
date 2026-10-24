#!/usr/bin/env python3
"""Bounded primary metadata fetch; never downloads toolchain binaries."""
import urllib.request,json,hashlib,time,resource,subprocess
from pathlib import Path
E=Path('evidence/sbf-identity-20261024');t=time.monotonic();rows=[]
urls={
 'platform-tag':'https://api.github.com/repos/anza-xyz/platform-tools/git/ref/tags/v1.52',
 'platform-release':'https://api.github.com/repos/anza-xyz/platform-tools/releases/tags/v1.52',
 'platform-build':'https://raw.githubusercontent.com/anza-xyz/platform-tools/v1.52/build.sh',
 'platform-workflow':'https://raw.githubusercontent.com/anza-xyz/platform-tools/v1.52/.github/workflows/main.yml',
}
for name,url in urls.items():
 a=time.monotonic();row=dict(url=url)
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Aspis-SBF-identity-metadata'})
  with urllib.request.urlopen(req,timeout=30) as r:
   b=r.read(5000001);row.update(http_status=r.status,headers=dict(r.headers))
  row.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),exit=0)
  if len(b)<=5000000:(E/(name+'.txt')).write_bytes(b)
 except Exception as ex:row.update(exit=1,error=str(ex))
 row['wall_seconds']=time.monotonic()-a;rows.append(row)
u=resource.getrusage(resource.RUSAGE_SELF)
(E/'official-fetch-receipt.json').write_text(json.dumps(dict(command=['python3','tools/sbf-identity-20261024/fetch-official.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),results=rows,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: metadata only'),indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k!='headers'} for r in rows],indent=2))
