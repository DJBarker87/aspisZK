"""Collect immutable inputs and receipts without launching another build."""
from pathlib import Path
import json,hashlib,re,subprocess
from run import H
R=H/'resume18';paths=[];lean=[];native=[]
for root in H.glob('lean-797*'):
 m=re.fullmatch(r'lean-(\d+)(?:-r\d+)?',root.name)
 if not m or int(m[1])<79766:continue
 paths.extend(p for p in root.rglob('*')if p.is_file())
 q=root/'receipt/receipt.json'
 if q.exists():lean.append(json.loads(q.read_text()))
for n in [79186,79187,79188,79189]:
 root=R/f'N{n}';paths.extend(p for p in root.rglob('*')if p.is_file());native.append(dict(label=root.name,**json.loads((root/'receipt/receipt.json').read_text())))
for n in ['std569-next','std569-range-next']:paths.extend(p for p in (R/n).rglob('*')if p.is_file())
paths.extend(H/'source'/p.name for p in (H/'source').glob('NEP_b3p6*_REACHABLE.txt'))
paths.extend(H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18_d569.py','audit_runtime569.py','std569_next_host.py','std569_range_host.py'])
paths.append(R/'std569-source-revision')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True);assert '0 loaded units listed'in scopes
objects=[]
for r in lean:
 if r['exit_status']!=0 or '--run'in r.get('command',[]) or 'NEPDriver'in r['module'] or 'NEPCohort'in r['module']:continue
 p=H/'lean-objects'/(r['module']+'.olean');assert p.exists()
 for dep,d in r['dependency_objects'].items():assert sha(Path(d['path']))==d['sha256']
 objects.append(dict(module=r['module'],object_sha256=sha(p),source_sha256=r['source_sha256'],attempt=r['attempt'],dependency_objects=r['dependency_objects']))
t=json.loads((H/'TALLY-resume18.json').read_text());paths=list(dict.fromkeys(paths));x=dict(hashes={str(p.relative_to(H)):sha(p)for p in paths},scopes=scopes,new_lean_receipts=len(lean),lean_success=sum(r['exit_status']==0 for r in lean),failures=[r['attempt']for r in lean if r['exit_status']!=0],new_extraction=len(native),native=[{k:r[k]for k in ['label','exit_status','wall_seconds','peak_rss_kib','swaps']}for r in native],new_kani=0,objects=objects,lean_attempts=t['lean_attempts'],next_lean=t['next_unused_id'],budget=dict(original_lean_remaining=180-t['lean_attempts'],new_906xx_block_remaining=100,extraction_remaining=3,kani_remaining=25),raw_audits=[79770,79780],guard_sha256=sha(H/'compile_resume18_d569.py'),full_frozen_manifest_run=False)
(R/'D569-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n');paths.append(R/'D569-final-host-inventory.json');(R/'D569-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\n');print(json.dumps({k:x[k]for k in ['new_lean_receipts','lean_success','failures','new_extraction','budget']}))
