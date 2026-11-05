from pathlib import Path
import subprocess,json,hashlib,shutil,sys
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair5-20261107')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104/NIQ_exports_20261107/objects')
with (B/'NIQ_EXPORT-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NIQ_EXPORT-admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((B/'NIQ_EXPORT-admission.json').read_text())
if r.returncode or ad.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,reservation=ad)));sys.exit(78)
C.mkdir(parents=True,exist_ok=True);rows=[]
for p in sorted((B/'NIQ_objects').glob('NIQ_*.olean')):
 if p.stem=='NIQ_Inspect':continue
 q=C/p.name;shutil.copy2(p,q)
 rows.append(dict(module=p.stem,path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
# All proof processes have ended; only own rebuildable products are removed.
removed=[]
for n in ['NIQ_target','NIQ_tmp','NIQ_objects','NIQ_native']:
 p=B/n
 if not p.exists():continue
 size=sum(q.stat().st_size for q in p.rglob('*')if q.is_file())
 shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
x=dict(admission=ad,files=rows,total_bytes=sum(r['bytes']for r in rows),removed_rebuildable=removed,cache_retained=True,source_scratch_retained=True)
(B/'NIQ_EXPORT.json').write_text(json.dumps(x,indent=2));print(json.dumps(x))
