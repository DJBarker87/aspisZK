"""Freeze and collect existing D543 receipts; never resubmit a job."""
from pathlib import Path
import json,hashlib,subprocess
from run import H
R=H/'resume18';paths=[]
for root in [*H.glob('lean-790*'),R]:
 if root==R:
  paths.extend(p for p in R.rglob('*')if p.is_file()and not any(part.endswith('-tmp')for part in p.parts)and p.name not in ['D546-final-host-inventory.json','D546-collect-paths.txt'])
 else:paths.extend(p for p in root.rglob('*')if p.is_file())
paths += [H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18.py','preflight_resume18_host.py','kani543_host.py','kani_inner227_resume18_host.py','reference_extract543_host.py','scan_ids_d543_host.py','reference_extract546_host.py','reference_callers546_host.py','kani546_host.py','queue_lean546_host.py']]
paths=[p for p in dict.fromkeys(paths) if not(p.name.endswith(('.tar','.tar.gz','.tgz','.olean','.o','.so','.bin')))]
assert all(p.is_file()for p in paths)
x=dict(hashes={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True),lean_attempts=json.loads((H/'TALLY-resume18.json').read_text())['lean_attempts'],extraction_receipts=len(list(R.glob('N*/receipt/receipt.json'))),kani_receipts=len(list(R.glob('K*/receipt/receipt.json'))))
assert '0 loaded units listed'in x['scopes'],x['scopes']
(R/'D546-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n')
(R/'D546-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\nresume18/D546-final-host-inventory.json\n')
print(json.dumps({k:x[k]for k in ['lean_attempts','extraction_receipts','kani_receipts']}))
