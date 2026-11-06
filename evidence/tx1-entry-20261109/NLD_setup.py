"""Seed only this job's workspace; retain predecessor caches read-only."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx1-entry-20261109'
seeds=[('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJN_exports_20261108_ee4038fa99e9','NJN'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKW_20261109/NKW_exports_20261109','NKW')]
paths=[B+'/NLD_seed/NJN',B+'/NLD_seed/NKW']+json.loads((E.parent/'ledger20-20261109/NKW_PATHS.json').read_text())
paths+=json.loads((E.parent/'entry-sdk-20261108/NJN_L026.json').read_text())['env']['LEAN_PATH'].split(':')
(E/'NLD_PATHS.json').write_text(json.dumps(list(dict.fromkeys(paths)),indent=1)+'\n')
code='''from pathlib import Path
import subprocess,json,sys,shutil,hashlib,lzma
b=Path(B);b.mkdir(exist_ok=True)
disk=shutil.disk_usage(b);assert disk.free>=40_000_000_000, 'disk below40GB'
with (b/'NLD_seed-admission.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NLD_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NLD_seed-admission.json';a=json.loads(p.read_text())if p.exists()else None
if r.returncode!=0 or not a or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
rows=[]
for src,tag in seeds:
 for p in sorted(Path(src).rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(src);q=b/'NLD_seed'/tag/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(path=str(p),destination=str(q),bytes=q.stat().st_size,sha256=h))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
for n in ['NLD_objects','NLD_generated','NLD_tmp','NLD_target']:(b/n).mkdir(exist_ok=True)
x=dict(files=rows,bytes=sum(r['bytes']for r in rows),admission=a,exit=r.returncode,disk=disk._asdict())
(b/'NLD_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()))
print(json.dumps(dict(files=len(rows),bytes=x['bytes'],disk=x['disk'])))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nseeds='+repr(seeds)+'\n'+code,text=True,capture_output=True)
(E/'NLD_SETUP.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr);assert r.returncode==0
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NLD_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0
(E/'NLD_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
