from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
request=json.loads((E/'NIG_NHT_IMPORT_REQUEST.json').read_text())
code='''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair4-20261107');dest=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104/NIG_NHT_seed')
with (b/'NIG_NHT_IMPORT-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIG_NHT_IMPORT-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NIG_NHT_IMPORT-admission.json';print(p.read_text()if p.exists()else'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode or json.loads(p.read_text()).get('allowed')is not True:sys.exit(78)
dest.mkdir(exist_ok=True);pins=[]
for row in request['rows']:
 candidates=[Path(row['path'])]+[Path(e['destination'])for e in request['exports']if e['sha256']==row['sha256']]
 source=next((p for p in candidates if p.is_file()and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']),None)
 assert source is not None,('retained input missing',row)
 suffix='.olean'+str(source).split('.olean',1)[1]
 out=dest/(row['module'].replace('.','/')+suffix);out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists():assert hashlib.sha256(out.read_bytes()).hexdigest()==row['sha256']
 else:shutil.copy2(source,out)
 pins.append(dict(row,actual_source=str(source),copied_to=str(out)))
(b/'NIG_NHT_IMPORTED.json').write_text(json.dumps(dict(files=len(pins),bytes=sum(p['bytes']for p in pins),pins=pins),indent=2))
print('IMPORTED',len(pins),flush=True)
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='request='+repr(request)+'\n'+code,text=True,capture_output=True)
(E/'NIG_NHT_IMPORT.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr)
if r.returncode:raise SystemExit(r.returncode)
for n in ['NIG_NHT_IMPORTED.json','NIG_NHT_IMPORT-admission.json','NIG_NHT_IMPORT-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-slice-d-pair4-20261107/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
