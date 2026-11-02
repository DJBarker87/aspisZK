"""Collect only the D557 continuation; no proof launches or cache changes."""
from run import H
from pathlib import Path
import re,json,hashlib,subprocess
R=H/'resume18';paths=[];latest={};all_receipts=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for root in H.glob('lean-*'):
 m=re.fullmatch(r'lean-(\d+)(?:-r\d+)?',root.name)
 if not m or not 79717<=int(m[1])<=79799:continue
 paths.extend(p for p in root.rglob('*')if p.is_file())
 q=root/'receipt/receipt.json'
 if q.exists():
  r=json.loads(q.read_text());all_receipts.append(r)
  if r['exit_status']==0 and (r['module']not in latest or r['attempt']>latest[r['module']]['attempt']):latest[r['module']]=r
objects=[]
for module,r in latest.items():
 src=H/'lean'/(module.replace('.','/')+'.lean');obj=H/'lean-objects'/(module.replace('.','/')+'.olean')
 assert sha(src)==r['source_sha256'],module
 for dep,d in r['dependency_objects'].items():assert sha(Path(d['path']))==d['sha256'],(module,dep)
 objects.append(dict(module=module,attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=sha(obj),dependency_objects=r['dependency_objects']))
(R/'D557-accepted-object-inventory.json').write_text(json.dumps(dict(objects=objects,dependency_mismatches=[]),indent=2)+'\n')
paths.extend(R/n for n in ['B3Q-COHORT-REUSE-D557.json','RUNJOIN-COHORT-RECONCILIATION-D557.json','environment-exceptions-D557.json','D557-accepted-object-inventory.json'])
paths.extend(H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18_extended.py'])
paths=list(dict.fromkeys(paths));assert all(p.is_file()for p in paths)
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True);assert '0 loaded units listed'in scopes,scopes
x=dict(hashes={str(p.relative_to(H)):sha(p)for p in paths},scopes=scopes,new_receipts=len(all_receipts),passes=sum(r['exit_status']==0 for r in all_receipts),failures=sum(r['exit_status']!=0 for r in all_receipts),lean_attempts=json.loads((H/'TALLY-resume18.json').read_text())['lean_attempts'],guard_sha256=sha(H/'compile_resume18_extended.py'),full_frozen_manifest_run=False,extraction_new=0,kani_new=0)
(R/'D557-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n');(R/'D557-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\nresume18/D557-final-host-inventory.json\n');print(json.dumps({k:x[k]for k in ['new_receipts','passes','failures','lean_attempts','full_frozen_manifest_run']}))
