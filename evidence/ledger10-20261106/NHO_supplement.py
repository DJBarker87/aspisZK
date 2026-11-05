from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger10-20261106';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NHO_flat'
files=json.loads((E/'NHO_SUPPLEMENT_INPUTS.json').read_text())
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
b=Path(B);c=Path(C)
with (b/'NHO_SUPPLEMENT_barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHO_SUPPLEMENT_admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NHO_SUPPLEMENT_admission.json').read_text())
if r.returncode!=0 or a.get('allowed')is not True:print(json.dumps(a));sys.exit(78)
out=[]
for root in set(str(Path(f['source']).parent)for f in files)|{'/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104/NFG_NFF_objects','/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104/NEV_exports_20261104'}:
 for p in Path(root).rglob('*.olean'):
  files.append(dict(source=str(p),relative=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for f in files:
 p=Path(f['source']);q=c/p.name
 assert p.is_file()and hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],str(p)
 for source in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not source.is_file():continue
  rel=Path(f.get('relative',p.name));q=c/rel.parent/source.name;q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(source.read_bytes()).hexdigest()
  if q.exists():
   if hashlib.sha256(q.read_bytes()).hexdigest()!=h:continue
  else:shutil.copy2(source,q)
  out.append(dict(source=str(source),destination=str(q),sha256=h,bytes=q.stat().st_size))
(b/'NHO_SUPPLEMENT_FINAL.json').write_text(json.dumps(dict(files=out,admission=a,exit=r.returncode),indent=1));print(len(out))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+code,capture_output=True,text=True)
 (E/f'NHO_SUPPLEMENT4_TRANSPORT_{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout,r.stderr,flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NHO_SUPPLEMENT_FINAL.json','NHO_SUPPLEMENT_admission.json','NHO_SUPPLEMENT_barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
