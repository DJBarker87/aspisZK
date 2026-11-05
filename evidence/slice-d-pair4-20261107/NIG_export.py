from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
mods=json.loads((E/'NIG_QUALIFIED_MODULES.json').read_text())+['NIG_COMBINED_IMPORT','NIG_FINAL_STATEMENTS','NIG_Driver','NIG_ProofDriver']
code=r"""
from pathlib import Path
import hashlib,shutil,json,subprocess,sys
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair4-20261107')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104')
ad=B/'NIG_export-reservation.json'
r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(ad)],capture_output=True,text=True)
j=json.loads(ad.read_text())
if r.returncode!=0 or j.get('allowed')is not True:
 print(json.dumps(dict(admission=dict(exit=r.returncode,reservation=j),launched=False)));sys.exit(78)
mods=MODS
rows=[];dst=C/'NIG_exports_20261107/objects';dst.mkdir(parents=True,exist_ok=True)
for m in mods:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NIG_objects'/(m+suffix)
  if not p.exists():continue
  q=dst/p.name
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(module=m,path=str(q),sha256=h,bytes=q.stat().st_size))
pins=dict(admission=dict(exit=r.returncode,reservation=j),exports=rows,total_bytes=sum(x['bytes']for x in rows),cache_retained=True)
(B/'NIG_EXPORT.json').write_text(json.dumps(pins,indent=2)+'\n')
removed=[]
# Only this job's rebuildable generated objects and target/temp products.
for name in ['NIG_target','NIG_objects','NIG_tmp']:
 p=B/name
 if p.exists():
  size=sum(f.stat().st_size for f in p.rglob('*')if f.is_file())
  shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
for p in (B/'NIG_native').iterdir():
 if p.is_file()and (p.suffix=='.c' or p.name in ['NIG_ProofDriver','NIG_Driver']):
  removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
cleanup=dict(removed=removed,cache_deleted=False,keys_touched=False,disk=subprocess.check_output(['df','-h',str(B)],text=True))
(B/'NIG_HOST_CLEANUP.json').write_text(json.dumps(cleanup,indent=2)+'\n')
print(json.dumps(dict(exports=pins,cleanup=cleanup)))
""".replace('MODS',repr(mods))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NIG_export.log').write_text(r.stderr)
assert r.returncode==0,(r.returncode,r.stdout,r.stderr)
j=json.loads(r.stdout)
for n,k in [('NIG_EXPORT.json','exports'),('NIG_HOST_CLEANUP.json','cleanup')]:
 (E/n).write_text(json.dumps(j[k],indent=2)+'\n')
print(json.dumps(dict(objects=len(j['exports']['exports']),export_bytes=j['exports']['total_bytes'],cleaned=len(j['cleanup']['removed']))))
