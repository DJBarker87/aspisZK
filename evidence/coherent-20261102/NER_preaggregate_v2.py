"""Pin all selected kernel/IR files immediately before the final aggregation."""
import hashlib,json
from pathlib import Path
B=Path(__file__).resolve().parent
paths=[B,B/'objects',Path('/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028'),Path('/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
original=[json.loads(l) for l in (B/'NER_MANIFEST.jsonl').read_text().splitlines()]
rebuilt={r['module']:r for r in map(json.loads,(B/'NER_REBUILD_ROWS.jsonl').read_text().splitlines())}
assert len(rebuilt)==1387 and 'NDR_CombinedAudit' in rebuilt
rows=[];original_only=[]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
for r in original:
 for artifact in r['artifacts']:
  assert sha(Path(artifact['path']))==artifact['sha256'],artifact['path']
 m=r['module'];rel=m.replace('.','/')+'.olean'
 obj=next(root/rel for root in paths if (root/rel).is_file())
 expected=rebuilt[m]['object_sha256'] if m in rebuilt else r['artifacts'][0]['sha256']
 assert sha(obj)==expected,m
 files=[]
 for p in [obj,Path(str(obj)+'.server'),Path(str(obj)+'.private'),obj.with_suffix('.ir')]:
  if p.exists():
   digest=sha(p)
   baseline=next((a for a in r['artifacts'] if Path(a['path']).name==p.name),None)
   if baseline and m not in rebuilt:assert baseline['sha256']==digest,str(p)
   files.append({'path':str(p),'sha256':digest,'bytes':p.stat().st_size})
 rows.append({'module':m,'artifacts':files})
 selected={f['path'] for f in files}
 original_only.extend(a for a in r['artifacts'] if a['path'] not in selected)
rows.append({'module':None,'role':'retained read-only original objects replaced by overlay','artifacts':original_only})
walker=B/'NER_Walker.olean';assert sha(walker)=='41972f6b2ca5eadbe2caa799e1416234f9690a9aa5560351a69926baf4390c92'
lean=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
assert sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
rows.append({'module':None,'role':'audit helper and pinned Lean binary','artifacts':[{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size} for p in [walker,lean]]})
(B/'NER_PREAGG_OBJECTS_A901.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({'target_modules':len(original),'rebuilt':len(rebuilt),'files':sum(len(r['artifacts']) for r in rows)}))
