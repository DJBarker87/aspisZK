"""Read-only checkpoint of charged206 predecessor work and uncharged refusals."""
from pathlib import Path
import hashlib,json,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');R=H/'resume18';paths=[]
for n in [90631,90632,90633]:
 for root in sorted(H.glob(f'lean-{n}*')):
  if root.is_dir():paths.extend(p for p in root.rglob('*')if p.is_file())
paths.extend(H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','compile_resume18_d569.py','external-verification-resume18.json','cache-verification-resume18.json'])
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True);assert'0 loaded units listed'in scopes
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();t=json.loads((H/'TALLY-resume18.json').read_text());assert t['lean_attempts']==205
receipts=[json.loads(p.read_text())for p in paths if str(p).endswith('/receipt/receipt.json')];assert len(receipts)==2
refusals=[str(p.parent.relative_to(H))for p in paths if p.name=='refusal.json'];assert len(refusals)==7
x=dict(hashes={str(p.relative_to(H)):sha(p)for p in paths},scopes=scopes,charged_attempts=2,success=1,failed=[90631],refusals=refusals,lean_attempts=205,budget=dict(lean_units_remaining=75,extraction_remaining=3,kani_remaining=25),pending_retry_id=90633,numerical_next_unused_id=t['next_unused_id'],pending_compile_modules=['PV_B3P_IndexCursorFamily579227','PV_B3P_MetadataSource580227','PV_B3P_MetadataFamily580227'],pending_raw_audit='PV_B3P_NEPCohort580227 /24 roots; not launched',audited_local_coverage=357,prepared_uncredited_coverage=365,endpoint_discharged=False,full_frozen_manifest_run=False)
p=R/'D581-wip-host-inventory.json';p.write_text(json.dumps(x,indent=2)+'\n');paths.append(p);(R/'D581-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\n');print(json.dumps({k:x[k]for k in ['charged_attempts','success','failed','refusals','budget','pending_retry_id']}))
