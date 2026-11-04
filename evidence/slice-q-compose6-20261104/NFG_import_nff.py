from NFG_remote import *
from NFG_peer import load
import hashlib
assert not (E/'NFG_ACTIVE.json').exists()
d=load();latest={};pins={}
for line in d['NFF_ATTEMPTS.jsonl'].decode().splitlines():
 r=json.loads(line)
 if r.get('kind')=='lean':latest[r['module']]=r
 pins.update({v['path']:v['sha256'] for v in r.get('deps_fingerprint',{}).get('selected_objects',{}).values()})
accepted={}
for m,r in latest.items():
 if r['exit_status']!=0 or not m.startswith('NFF_'):continue
 source=d[m+'.lean'];path='NFF_generated/'+m+'.lean'
 assert hashlib.sha256(source).hexdigest()==r['source_hashes'][path],('peer source drift',m)
 for s in r['print_axioms']:
  assert 'sorryAx' not in s and '.ax_' not in s,s
 accepted[m]=dict(receipt=r['attempt'],source_sha256=hashlib.sha256(source).hexdigest(),source=source.decode())
a='NFG_IMPORT_NFF';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json,shutil
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul7-cache-20261029');out=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose6-cache-20261104/NFG_NFF_objects');out.mkdir(exist_ok=True)
roots=[c/'NFF_exports_20261104']+[c/n for n in ['NER_cohort','NFE_exports_20261104','NFC_audit_support_20261104','NFC_exports_20261104','NFA_exports_20261104','NEV_exports_20261104','NEI_exports_20261103','NEG_results_20261101','NEG_exports_20261029','NEB_exports_20261029']]
standard={{'Aeneas','AeneasMeta','Mathlib','Aesop','Batteries','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lean','Init','Std'}}
accepted={accepted!r};known={pins!r};rows=[]
for root in roots:
 for p in sorted(root.rglob('*')):
  if not p.is_file() or not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  rel=p.relative_to(root)
  if rel.parts[0].split('.')[0] in standard:continue
  if root==roots[0] and p.stem.split('.')[0] not in accepted:continue
  q=out/rel
  if q.exists():continue
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if str(p) in known:assert known[str(p)]==h,('peer object drift',str(p))
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=h,receipt_pin=str(p) in known,bytes=p.stat().st_size))
# Pin exact committed source bytes for every own peer object, never a live worktree.
for m,v in accepted.items():
 p=out/(m+'.lean');p.write_text(v['source']);assert hashlib.sha256(p.read_bytes()).hexdigest()==v['source_sha256']
print(json.dumps(dict(objects=rows,modules={{m:{{k:v[k] for k in ['receipt','source_sha256']}} for m,v in accepted.items()}},library_provenance='221 common Aeneas objects compared byte-identical; coherent standard library retained')))
''');assert r.returncode==0,r.stderr
new=json.loads(r.stdout)
p=E/'NFG_NFF_OBJECT_IMPORTS.json'
if p.exists():
 old=json.loads(p.read_text());new['objects']=old['objects']+new['objects']
p.write_text(json.dumps(new,indent=1)+'\n')
