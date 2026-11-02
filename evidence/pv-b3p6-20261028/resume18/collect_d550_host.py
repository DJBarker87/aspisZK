"""Freeze and collect existing D543 receipts; never resubmit a job."""
from pathlib import Path
import json,hashlib,subprocess
from run import H
R=H/'resume18';paths=[]
latest={}
for receipt in H.glob('lean-790*/receipt/receipt.json'):
 row=json.loads(receipt.read_text())
 if row.get('exit_status')==0 and 79028<=row.get('attempt',0)<=79096:
  if row['module']not in latest or row['attempt']>latest[row['module']]['attempt']:latest[row['module']]=row
objects=[]
for module,row in latest.items():
 src=H/'lean'/(module+'.lean');obj=H/'lean-objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==row['source_sha256'],module
 assert obj.is_file(),module
 for dep,rec in row['dependency_objects'].items():assert hashlib.sha256(Path(rec['path']).read_bytes()).hexdigest()==rec['sha256'],(module,dep)
 objects.append(dict(module=module,attempt=row['attempt'],source_sha256=row['source_sha256'],object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),dependency_fingerprint=row['deps_fingerprint']))
(R/'D550-accepted-object-inventory.json').write_text(json.dumps(dict(objects=objects,dependency_mismatches=[]),indent=2)+'\n')
for root in [*H.glob('lean-790*'),R]:
 if root==R:
  paths.extend(p for p in R.rglob('*')if p.is_file()and not any(part.endswith('-tmp')for part in p.parts)and p.name not in ['D550-final-host-inventory.json','D550-collect-paths.txt'])
 else:paths.extend(p for p in root.rglob('*')if p.is_file())
paths += [H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18.py','preflight_resume18_host.py','kani543_host.py','kani_inner227_resume18_host.py','reference_extract543_host.py','scan_ids_d543_host.py','reference_extract546_host.py','reference_callers546_host.py','kani546_host.py','queue_lean546_host.py','scan_ids_d546_host.py','queue_lean547_host.py','reference_packed547_host.py','kani547_host.py','reference_projected547_host.py']]
paths += [p for p in H.glob('*550*.py') if p.is_file()]
paths += [H/'run.py', H/'capped.py']
paths=[p for p in dict.fromkeys(paths) if not(p.name.endswith(('.tar','.tar.gz','.tgz','.olean','.o','.so','.bin')))]
assert all(p.is_file()for p in paths)
x=dict(hashes={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True),lean_attempts=json.loads((H/'TALLY-resume18.json').read_text())['lean_attempts'],extraction_receipts=len(list(R.glob('N*/receipt/receipt.json'))),kani_receipts=len(list(R.glob('K*/receipt/receipt.json'))))
assert '0 loaded units listed'in x['scopes'],x['scopes']
(R/'D550-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n')
(R/'D550-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\nresume18/D550-final-host-inventory.json\n')
print(json.dumps({k:x[k]for k in ['lean_attempts','extraction_receipts','kani_receipts']}))
