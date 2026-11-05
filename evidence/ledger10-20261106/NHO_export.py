"""Retain only own import objects; pin all actually resolved modules, including Aeneas."""
from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger10-20261106';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NHO_flat'
code='''from pathlib import Path
import json,hashlib,lzma,shutil,subprocess,sys
b=Path(B);c=Path(C);export=c/'NHO_exports_20261106'
with (b/'NHO_EXPORT_barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHO_EXPORT_admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((b/'NHO_EXPORT_admission.json').read_text())
if r.returncode!=0 or ad.get('allowed')is not True:print(json.dumps(ad));sys.exit(78)
export.mkdir(exist_ok=True);copied=[]
for p in (b/'NHO_objects').glob('*'):
 if p.is_file():
  q=export/p.name
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==hashlib.sha256(p.read_bytes()).hexdigest()
  else:shutil.copy2(p,q)
  copied.append(dict(source=str(p),path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
x=json.loads((b/'NHO_L010.json').read_text());roots=x['env']['LEAN_PATH'].split(':');modules=[json.loads(l)['module']for l in(b/'NHO_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
for module in modules:
 rel=module.replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,module
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=module,path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins,modules=len(modules))).encode();(b/'NHO_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(b/'NHO_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
(b/'NHO_EXPORT.json').write_text(json.dumps(dict(export=str(export),files=copied,bytes=sum(p['bytes']for p in copied),admission=ad,exit=r.returncode,cache_retained=str(c),binaries_exported=False),indent=1));print(json.dumps(dict(exports=len(copied),closure_objects=len(pins))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\n'+code,capture_output=True,text=True)
 (E/f'NHO_EXPORT_TRANSPORT_{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout,r.stderr,flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NHO_CLOSURE_PINS.json.xz','NHO_CLOSURE_PINS.json.sha256','NHO_EXPORT.json','NHO_EXPORT_admission.json','NHO_EXPORT_barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
