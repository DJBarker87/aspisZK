"""Prepare an informational release bundle privately; no adopted tool changes."""
from pathlib import Path
import urllib.request,json,hashlib,tarfile
B=Path.cwd();D=B/'NMD_newest';D.mkdir(exist_ok=True)
url='https://api.github.com/repos/model-checking/kani/releases/latest'
x=json.load(urllib.request.urlopen(url,timeout=30));a=next(a for a in x['assets'] if a['name'].endswith('x86_64-unknown-linux-gnu.tar.gz'))
archive=D/a['name']
if not archive.exists():
 with urllib.request.urlopen(a['browser_download_url'],timeout=60) as r,archive.open('wb') as f:
  while block:=r.read(1024*1024):f.write(block)
with tarfile.open(archive) as t:t.extractall(D,filter='data')
out=dict(release_api=url,release_url=x['html_url'],tag=x['tag_name'],published_at=x['published_at'],asset_url=a['browser_download_url'],bytes=archive.stat().st_size,sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),informational_only=True)
(B/'NMD_NEWEST_PIN.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
