from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-finish2-20261105';C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104';H='dombarker@100.108.41.90'
files={}
for a,b in [('NFA_WALKER','NGW_WALKER'),('NFA_MemoryLimit','NGW_MemoryLimit')]:
 data=(E.parent/'slice-d-check-20261104/NFU_L059/sources/NFU_native'/(a+'.c')).read_text();(E/(b+'.c.txt')).write_text(data);files['NGW_native/'+a+'.c']=data
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
b=Path(B);c=Path(C)
with (b/'NGW_AUDIT_SETUP-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGW_AUDIT_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NGW_AUDIT_SETUP-admission.json';print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
pins=[];seed=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104')
for module in ['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations']:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  src=seed/(module+suffix)
  if src.is_file():
   dest=c/(module+suffix)
   if not dest.exists():shutil.copy2(src,dest)
   assert dest.read_bytes()==src.read_bytes();pins.append(dict(source=str(src),destination=str(dest),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bytes=src.stat().st_size))
for n,t in files.items():p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t);pins.append(dict(destination=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(b/'NGW_AUDIT_SETUP-pins.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(files=len(pins))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+code,text=True,capture_output=True)
 (E/f'NGW_AUDIT_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==79 and retry==0:time.sleep(30);continue
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.stdout+r.stderr)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NGW_AUDIT_SETUP-pins.json','NGW_AUDIT_SETUP-admission.json','NGW_AUDIT_SETUP-admission.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
