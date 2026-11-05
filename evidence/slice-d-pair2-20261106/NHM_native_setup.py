from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-pair2-20261106';H='dombarker@100.108.41.90'
import runpy
prepared=runpy.run_path(str(E/'NHM_native_prepare.py'));files=prepared['inputs'];pins=prepared['pins']
remote='''from pathlib import Path
import json,subprocess,sys,shutil
b=Path(B)
with (b/'NHM_SETUP-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHM_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NHM_SETUP-admission.json';print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
s=b/'NHM_src'
if not s.exists():shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-finish-20261105/NGM_src',s,ignore=shutil.ignore_patterns('target','.git'))
for n,t in files.items():p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NHM_SOURCE_PINS.json').write_text(json.dumps(pins))
print('scratch ready')
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nfiles='+repr(files)+'\npins='+repr(pins)+'\n'+remote,text=True,capture_output=True)
 (E/f'NHM_SETUP-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-350:],r.stderr[-1000:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,79,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(30 if r.returncode==79 else 60 if r.returncode==255 else 180)
