"""Collect this continuation's receipts and immutable inputs; never relaunch."""
from run import H
from pathlib import Path
import json,re,hashlib,subprocess
R=H/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();paths=[];lean=[];native=[]
for root in H.glob('lean-797*'):
 match=re.fullmatch(r'lean-(\d+)(?:-r\d+)?',root.name)
 if not match or int(match[1])<79732:continue
 paths.extend(p for p in root.rglob('*')if p.is_file())
 p=root/'receipt/receipt.json'
 if p.exists():lean.append(json.loads(p.read_text()))
for root in R.glob('N791*'):
 match=re.fullmatch(r'N(\d+)(?:-r\d+)?',root.name)
 if not match or int(match[1])<79168:continue
 paths.extend(p for p in root.rglob('*')if p.is_file())
 p=root/'receipt/receipt.json'
 if p.exists():native.append(dict(label=root.name,**json.loads(p.read_text())))
for name in ['opaque559','std559','std559-nocopy','std559-readrange','std559-range','std559-nth']:
 paths.extend(p for p in (R/name).rglob('*')if p.is_file())
paths.extend(R/n for n in ['opaque559-upstream-command.json','std559-source-revision'])
paths.extend(H/n for n in ['TALLY-resume18.json','project-resolution-resume18.json','external-verification-resume18.json','cache-verification-resume18.json','compile_resume18_extended.py','opaque559_host.py','std559_host.py','std559_nocopy_host.py','std559_readrange_host.py','std559_range_host.py','std559_nth_host.py','queue_d559_host.py'])
latest={}
for r in sorted(lean,key=lambda r:r['attempt']):
 if r['exit_status']==0:latest[r['module']]=r
objects=[]
for m,r in latest.items():
 p=H/'lean-objects'/(m.replace('.','/')+'.olean');s=H/'lean'/(m.replace('.','/')+'.lean')
 assert sha(s)==r['source_sha256'],m
 for dep,d in r['dependency_objects'].items():assert sha(Path(d['path']))==d['sha256'],(m,dep)
 objects.append(dict(module=m,attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=sha(p),dependency_objects=r['dependency_objects'],quarantined=m=='PV_B3P_Std559Funs227'))
(R/'D559-accepted-object-inventory.json').write_text(json.dumps(dict(objects=objects,dependency_mismatches=[]),indent=2)+'\n');paths.append(R/'D559-accepted-object-inventory.json')
scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True);assert '0 loaded units listed'in scopes,scopes
paths=list(dict.fromkeys(paths));assert all(p.is_file()for p in paths)
t=json.loads((H/'TALLY-resume18.json').read_text())
x=dict(hashes={str(p.relative_to(H)):sha(p)for p in paths},scopes=scopes,new_lean_receipts=len(lean),lean_zero=sum(r['exit_status']==0 for r in lean),lean_failed=[r['attempt']for r in lean if r['exit_status']!=0],lean_attempts=t['lean_attempts'],next_lean=t['next_unused_id'],refused=[r for r in t.get('refusals',[])if r['attempt']>=79732],retired_unsubmitted_lean=[i for i in t['used_ids']if i>=79732 and i not in [r['attempt']for r in lean]and i not in [r['attempt']for r in t.get('refusals',[])]],new_native_receipts=len(native),native_zero=sum(r['exit_status']==0 for r in native),native=[{k:r[k]for k in ['label','exit_status','wall_seconds','peak_rss_kib','swaps']}for r in native],new_kani=0,guard_sha256=sha(H/'compile_resume18_extended.py'),full_frozen_manifest_run=False,budget=dict(lean_remaining=180-t['lean_attempts'],extraction_remaining=22-len(native),kani_remaining=25),raw_module_quarantined='PV_B3P_Std559Funs227; native_decide literal-bound elaboration; only the independent kernel-normalized cohort is credited',unsubmitted_79749='own staging authority mismatch BEFORE scope launch; source pin corrected, no proof attempted, ID retained')
(R/'D559-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n');(R/'D559-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\nresume18/D559-final-host-inventory.json\n');print(json.dumps({k:x[k]for k in ['new_lean_receipts','lean_zero','lean_failed','new_native_receipts','native_zero','budget','retired_unsubmitted_lean']}))
