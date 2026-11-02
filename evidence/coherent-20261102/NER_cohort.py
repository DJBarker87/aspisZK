"""Pin the exact selected final cohort after the affected rebuild; no Lean invocation."""
import hashlib,json
from pathlib import Path
B=Path(__file__).resolve().parent
original=[json.loads(l) for l in (B/'NER_MANIFEST.jsonl').read_text().splitlines()]
sources={r['module']:r for r in map(json.loads,(B/'NER_UPSTREAM_SOURCE_PINS.jsonl').read_text().splitlines())}
rebuilt={r['module']:r for r in map(json.loads,(B/'NER_REBUILD_ROWS.jsonl').read_text().splitlines())}
rows=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for r in original:
 m=r['module'];rel=m.replace('.','/')+'.olean'
 obj=B/rel if (B/rel).exists() else Path(r['artifacts'][0]['path'])
 actual=sha(obj);new=rebuilt.get(m)
 assert actual==(new['object_sha256'] if new else r['artifacts'][0]['sha256']),m
 source=sources[m]
 if new:
  src=B/Path(rel).with_suffix('.lean');assert sha(src)==new['source_sha256'],m
  source={**source,'source_sha256':new['source_sha256'],'source_path':str(src),'source_basis':'unchanged pinned repository source, coherently rebuilt in NER overlay'}
 companions=[]
 for suffix in ['.server','.private']:
  p=Path(str(obj)+suffix)
  if p.exists():companions.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
 rows.append({**source,'object_path':str(obj),'object_sha256':actual,'object_bytes':obj.stat().st_size,'companions':companions,'rebuilt':new is not None,'imports':r['imports']})
(B/'NER_STREAM_B_COHORT.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({'modules':len(rows),'rebuilt':len(rebuilt),'all_sources_hashed':all(r['source_sha256'] for r in rows)}))
