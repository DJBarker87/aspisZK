from pathlib import Path
import json,subprocess,hashlib,lzma,shutil,sys
b=Path(B);q=b/'NHP_LEAN_SEED_RESERVATION.json'
with (b/'NHP_LEAN_SEED_RESERVATION.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads(q.read_text());print(json.dumps(dict(exit=r.returncode,allowed=ad.get('allowed'))),flush=True)
if r.returncode or ad.get('allowed') is not True:sys.exit(78)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');rows=[]
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=w/name;target=b/name;shutil.copy2(p,target);assert p.read_bytes()==target.read_bytes();rows.append(dict(source=str(p),destination=str(target),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
x=json.loads(Path('/home/dombarker/project-offloads/codex-cx-pool-leaves-20261105/NHC_EXPORT.json').read_text());imports=[]
for row in x['exports']:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 imports.append(dict(row,copied=False))
raw=json.dumps(dict(imports=imports,seed_bytes=0,reused_bytes=sum(r['bytes'] for r in imports),configuration_files=rows)).encode()
(b/'NHP_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NHP_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
for name in ['NHP_CACHE_IMPORTS.json.xz','NHP_CACHE_IMPORTS.json.sha256','NHP_LEAN_SEED_RESERVATION.json','NHP_LEAN_SEED_RESERVATION.log','NHP_SEED.json','NHP_NATIVE_SEED-admission.json','NHP_NATIVE_SEED-barrier.log']:
 p=b/name
 if p.is_file():import base64;print(json.dumps(dict(name=name,data=base64.b64encode(p.read_bytes()).decode())))
