"""Owned cache-copy validation; shared launchers are copied unchanged."""
from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-integrate-20261111'
paths=json.loads((E/'NNH_SEED_PATHS.json').read_text())
code='''from pathlib import Path
import subprocess,json,shutil,hashlib,lzma,sys
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NNH_seed-barrier.log').open('w') as log:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NNH_seed-admission.json')],stdout=log,stderr=subprocess.STDOUT)
p=b/'NNH_seed-admission.json'
if not p.exists(): print('MISSING');sys.exit(79)
ad=json.loads(p.read_text())
if r.returncode or ad.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,reservation=ad)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
out=b/'NNH_seed';out.mkdir(exist_ok=True);seen=set();rows=[];missing=[]
ledger=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111/NMQ_CLOSURE_PINS.json.xz')
selected=json.loads(lzma.decompress(ledger.read_bytes()))['selected_objects']
inputs=[]
for row in selected:
 p=Path(row['path']);stem=row['module'].replace('.','/')
 suffix=next(s for s in ['.olean.private','.olean.server','.olean','.ir'] if str(p).endswith(s))
 inputs.append((p,stem+suffix,row['sha256']))
# Additional sibling exports and direct module directories only. Never recurse
# through historical workspace/cache directories from a LEAN_PATH root.
for root in paths:
 root=Path(root)
 if not root.is_dir():missing.append(str(root));continue
 for p in sorted(root.iterdir()):
  if p.is_file() and any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):inputs.append((p,p.name,None))
for p,rel,expected in inputs:
 if rel in seen:continue
 seen.add(rel);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
 digest=hashlib.sha256(p.read_bytes()).hexdigest()
 assert expected is None or digest==expected,str(p)
 if not q.exists() or hashlib.sha256(q.read_bytes()).hexdigest()!=digest:shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==digest,str(q)
 rows.append(dict(path=str(p),destination=str(q),sha256=digest,bytes=q.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(w/n,b/n)
manifest=dict(missing_search_paths=missing,files=rows,admission=ad,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())
raw=json.dumps(manifest).encode();(b/'NNH_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),disk=manifest['disk'])))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\npaths='+repr(paths)+'\n'+code,text=True,capture_output=True)
 (E/f'NNH_seed-{retry}.log').write_text(r.stdout+r.stderr)
 print(r.stdout[-1000:]+r.stderr[-1000:],flush=True)
 if r.returncode==0:break
 if r.returncode in [78,79,255] and retry<10:time.sleep(180 if r.returncode==78 else 60 if r.returncode==255 else 30);continue
 raise RuntimeError('Seed failed; no scopes launched')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NNH_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0
(E/'NNH_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
