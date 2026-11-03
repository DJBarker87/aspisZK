"""Read-only library source inventory. Object identity is reported separately."""
from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/weighted-hensel-repair/.lake/packages')
roots=[Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean'),Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/s6-formatter-tool-v5/source/backends/lean')]+sorted(p for p in P.iterdir() if p.is_dir())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for line in (B/'NER_SOURCE_INVENTORY.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r['source_sha256'] is None:
  rel=r['module'].replace('.','/')+'.lean'
  candidates=[p/rel for p in roots if (p/rel).is_file()]
  if candidates:
   p=candidates[0];r.update(source_sha256=sha(p),source_path=str(p),source_basis='host library source inventory; reused object, no fresh upstream compilation')
   obj=p.parent
   root=next(rt for rt in roots if p==rt/rel)
   q=root/'.lake/build/lib/lean'/Path(rel).with_suffix('.olean')
   r['adjacent_build_object_sha256']=sha(q) if q.exists() else None
 rows.append(r)
(B/'NER_SOURCE_INVENTORY_HOST.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({'total':len(rows),'unlocated':[r['module'] for r in rows if r['source_sha256'] is None]}))
