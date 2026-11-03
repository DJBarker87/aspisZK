"""Read-only receipt collection after all focused scopes finish."""
from pathlib import Path
import json,hashlib,subprocess
from run import H
R=H/'resume18';paths=[];receipts=[];refusals=[]
ids=list(range(79792,79797))+list(range(90600,90609))
for n in ids:
 for root in sorted(H.glob(f'lean-{n}*')):
  if not root.is_dir():continue
  paths.extend(p for p in root.rglob('*')if p.is_file())
  q=root/'receipt/receipt.json'
  if q.exists():receipts.append(json.loads(q.read_text()))
  else:refusals.append(str(root.relative_to(H)))
paths.extend(p for p in (H/'source').glob('NEP_b3p6_cohort572*_REACHABLE.txt'))
paths.extend(H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18_d569.py','audit_runtime569.py'])
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True);assert '0 loaded units listed'in scopes
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
objects=[]
for r in receipts:
 if r['exit_status']!=0 or 'NEPCohort'in r['module']:continue
 p=H/'lean-objects'/(r['module']+'.olean');assert p.exists()
 for d in r['dependency_objects'].values():assert sha(Path(d['path']))==d['sha256']
 objects.append(dict(module=r['module'],attempt=r['attempt'],object_sha256=sha(p),source_sha256=r['source_sha256'],dependency_objects=r['dependency_objects']))
t=json.loads((H/'TALLY-resume18.json').read_text());assert t['lean_attempts']==181,t['lean_attempts']
x=dict(hashes={str(p.relative_to(H)):sha(p)for p in paths},objects=objects,scopes=scopes,charged_attempts=len(receipts),success=sum(r['exit_status']==0 for r in receipts),failed=[r['attempt']for r in receipts if r['exit_status']!=0],uncharged_scope_refusals=refusals,lean_attempts=t['lean_attempts'],next_lean=t['next_unused_id'],budget=dict(lean_units_remaining=280-t['lean_attempts'],extraction_remaining=3,kani_remaining=25),no_extraction_or_kani_launched=True,full_frozen_manifest_run=False,guard_sha256=sha(H/'compile_resume18_d569.py'))
p=R/'D572-final-host-inventory.json';p.write_text(json.dumps(x,indent=2)+'\n');paths.append(p);(R/'D572-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\n');print(json.dumps({k:x[k]for k in ['charged_attempts','success','failed','uncharged_scope_refusals','budget','next_lean']}))
