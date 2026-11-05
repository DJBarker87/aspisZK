from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
P=E.parent/'ledger11-20261107'
s=(P/'NII_run.py').read_text().replace('NII','NIM').replace('codex-cx-ledger11-20261107','codex-cx-owner-dedupe-20261107').replace("C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat'","C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat'")
s=s.replace("[B+'/NIM_objects',C,W,W+'/objects',T+'/lib/lean']","[B+'/NIM_objects',C,'/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NII_flat',W,W+'/objects',T+'/lib/lean']")
(E/'NIM_run.py').write_text(s)
(E/'NIM_InspectNFW.lean').write_text('import NFW_ErrorReferenceTypes\nset_option pp.all true\n#print instDiscriminantVerifierErrorIsize\n#print prefix NFW_ErrorReference\n')
(E/'NIM_InspectNGL.lean').write_text('import NGL_MapReference.Types\nset_option pp.all true\n#print instDiscriminantVerifierErrorIsize\n#print prefix NGL_MapReference\n')
code='''from pathlib import Path
import subprocess,json,shutil,hashlib,lzma,sys
b=Path('/home/dombarker/project-offloads/codex-cx-owner-dedupe-20261107');b.mkdir(exist_ok=True)
with (b/'NIM_SEED_BARRIER.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIM_SEED_ADMISSION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NIM_SEED_ADMISSION.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed')is not True:sys.exit(78)
c=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat');c.mkdir(exist_ok=True)
rows=[]
for p in Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NII_flat/NII_exports_20261107').rglob('*'):
 if p.is_file():
  q=c/p.name
  if not q.exists():shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(selected=rows,logical_bytes=sum(x['bytes']for x in rows),admission=a,exit=r.returncode)
(b/'NIM_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NIM_SEED.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr);assert r.returncode==0
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-owner-dedupe-20261107/NIM_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NIM_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
