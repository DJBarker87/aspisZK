"""Inventory and collect existing D554 artifacts; never launches proof work."""
from run import H
from pathlib import Path
import re,json,hashlib,subprocess
R=H/'resume18';paths=[];latest={}
for root in H.glob('lean-*'):
 m=re.fullmatch(r'lean-(\d+)(?:-r\d+)?',root.name)
 if not m or not(79071<=int(m[1])<=79096 or 79700<=int(m[1])<=79799):continue
 paths.extend(p for p in root.rglob('*')if p.is_file())
 receipt=root/'receipt/receipt.json'
 if receipt.exists():
  r=json.loads(receipt.read_text())
  if r['exit_status']==0 and (r['module']not in latest or r['attempt']>latest[r['module']]['attempt']):latest[r['module']]=r
objects=[]
for module,r in latest.items():
 src=H/'lean'/(module+'.lean');obj=H/'lean-objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256'],module
 assert obj.is_file(),module
 for dep,d in r['dependency_objects'].items():assert hashlib.sha256(Path(d['path']).read_bytes()).hexdigest()==d['sha256'],(module,dep)
 objects.append(dict(module=module,attempt=r['attempt'],object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),source_sha256=r['source_sha256'],deps_fingerprint=r['deps_fingerprint']))
(R/'D554-accepted-object-inventory.json').write_text(json.dumps(dict(objects=objects,dependency_mismatches=[]),indent=2)+'\n')
paths.extend(R/n for n in ['RECOVERY-D554.json','DEPLOYED-FEATURE-RECHECK-D554.json','D554-accepted-object-inventory.json'])
paths.extend(H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18_extended.py','queue_lean554_host.py','admission-not-before.json'])
paths=[p for p in dict.fromkeys(paths)if p.name.split('.')[-1]not in ['olean','o','so','tar','bin']]
assert all(p.is_file()for p in paths)
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True)
assert '0 loaded units listed'in scopes,scopes
x=dict(hashes={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},scopes=scopes,lean_attempts=json.loads((H/'TALLY-resume18.json').read_text())['lean_attempts'],extraction_receipts=len(list(R.glob('N*/receipt/receipt.json'))),kani_receipts=len(list(R.glob('K*/receipt/receipt.json'))))
(R/'D554-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n')
(R/'D554-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\nresume18/D554-final-host-inventory.json\n')
print(json.dumps(dict(hashes=len(paths),lean_attempts=x['lean_attempts'],accepted=len(objects))))
