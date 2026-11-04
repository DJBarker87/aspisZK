"""Freeze exact scope receipts and NEP walks; never collect build objects."""
from pathlib import Path
import hashlib,json,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');R=H/'resume18';paths=[]
for n in range(90665,90697):
 for root in sorted(H.glob(f'lean-{n}*')):
  if root.is_dir():paths.extend(p for p in root.rglob('*')if p.is_file())
paths.extend(p for p in (H/'source').glob('NEP_b3p6_cohort592_*')if p.is_file())
for n in ['TALLY-resume18.json','project-resolution-resume18.json','compile_resume18_d569.py','external-verification-resume18.json','cache-verification-resume18.json','admission-not-before.json']:
 p=H/n
 if p.exists():paths.append(p)
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True)
assert '0 loaded units listed'in scopes,scopes
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();t=json.loads((H/'TALLY-resume18.json').read_text())
receipts=[json.loads(p.read_text())for p in paths if str(p).endswith('/receipt/receipt.json')]
refusals=[str(p.parent.relative_to(H))for p in paths if p.name=='refusal.json'];cooldown_refusals=[str(p.parent.relative_to(H))for p in paths if p.name=='cooldown-refusal.json']
quiet=H.parent/'QUIET_WINDOW.json';quiet_state=dict(now=time.time(),path=str(quiet),marker=json.loads(quiet.read_text())if quiet.exists()else None)
x=dict(quiet_window=quiet_state,hashes={str(p.relative_to(H)):sha(p)for p in paths},scopes=scopes,charged_attempts=len(receipts),success=sum(r['exit_status']==0 for r in receipts),failed=[r['attempt']for r in receipts if r['exit_status']!=0],refusals=refusals,cooldown_refusals=cooldown_refusals,lean_attempts=t['lean_attempts'],budget=dict(lean_units_remaining=280-t['lean_attempts'],extraction_remaining=3,kani_remaining=25),numerical_next_unused_id=t['next_unused_id'],endpoint_discharged=False,full_frozen_manifest_run=False)
p=R/'D592-host-inventory.json';p.write_text(json.dumps(x,indent=2)+'\n');paths.append(p);(R/'D592-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\n')
print(json.dumps({k:x[k]for k in ['charged_attempts','success','failed','refusals','budget']}))
