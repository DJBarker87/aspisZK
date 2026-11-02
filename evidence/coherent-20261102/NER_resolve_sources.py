"""Resolve duplicate repository source locations by exact module path and content hash."""
import hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent.parent
rows=[json.loads(l) for l in (E/'NER_SOURCE_INVENTORY_HOST.jsonl').read_text().splitlines()]
needed={p for r in rows if not r['source_sha256'] for p in r.get('candidates',[]) if p.endswith('/'+r['module'].replace('.','/')+'.lean') or '.' not in r['module']}
p=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
hashes={}
for path in sorted(needed):
 p.stdin.write(('HEAD:'+path+'\n').encode());p.stdin.flush();header=p.stdout.readline().decode().split();n=int(header[2]);data=p.stdout.read(n);assert p.stdout.read(1)==b'\n';hashes[path]=hashlib.sha256(data).hexdigest()
p.stdin.close();p.wait()
for r in rows:
 if r['source_sha256']:continue
 ps=[p for p in r.get('candidates',[]) if p in hashes]
 vals={hashes[p] for p in ps}
 if len(vals)==1:
  r.update(source_sha256=next(iter(vals)),source_path=ps[0],source_basis='byte-identical repository source copies; unchanged upstream object reused')
  r['source_copies']=ps
 elif ps:
  r['candidate_sha256']={p:hashes[p] for p in ps}
(E/'NER_SOURCE_RESOLVED.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({'total':len(rows),'unresolved':[r['module'] for r in rows if not r['source_sha256']]}))
