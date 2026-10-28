"""Read-only recovery of exact, deduplicated textual per-attempt snapshots."""
import sys,json,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import KMY_host as h
code='''from pathlib import Path
import hashlib,json
b=Path('''+repr(h.B)+'''); unique={}; attempts={}
for p in sorted(b.glob('KMY_*/receipt.json')):
 c=json.loads(p.read_text()); rows={}
 for name,sha in c['source_hashes'].items():
  q=p.parent/'sources'/name
  data=q.read_bytes();assert hashlib.sha256(data).hexdigest()==sha
  unique[sha]=data.decode();rows[name]=sha
 attempts[c['attempt']]=rows
cache=Path('/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028')
objects={p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in cache.glob('*.olean')}
print(json.dumps(dict(unique=unique,attempts=attempts,objects=objects)))
'''
r=h.remote_py(code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);dest=h.E/'sources';dest.mkdir(exist_ok=True)
for sha,data in out.pop('unique').items():
 assert hashlib.sha256(data.encode()).hexdigest()==sha
 (dest/(sha+'.txt')).write_text(data)
(h.E/'KMY_SOURCE_ARCHIVE.json').write_text(json.dumps(out,indent=2)+'\n')
print('archived',len(list(dest.glob('*.txt'))),'unique text sources;',len(out['attempts']),'attempts; cache retained')
