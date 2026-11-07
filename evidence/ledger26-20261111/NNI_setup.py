from pathlib import Path
import subprocess,json,time,lzma
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNI_20261111'
seeds=json.loads((E/'NNI_SEED_INPUTS.json').read_text())
code='''from pathlib import Path
import json,subprocess,sys,hashlib,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NNI_seed-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NNI_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NNI_seed-admission.json'
if not p.exists():sys.exit(79)
a=json.loads(p.read_text())
if r.returncode or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
rows=[]
for row in seeds:
 p=Path(row['path']);assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 # Retain all matching sidecars, whose hashes are recorded now.
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not src.is_file():continue
  rel=str(src)[len(str(p))-len(row['relative']):]
  q=b/(row['tag']+'_seed')/rel;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(src,q)
  h=hashlib.sha256(src.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(tag=row['tag'],path=str(src),destination=str(q),sha256=h,bytes=src.stat().st_size))
native=b/'NNI_native';native.mkdir(exist_ok=True)
source=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111/NMQ_native/NMQ_ProofDriver')
shutil.copy2(source,native/'NNI_ProofDriver')
rows.append(dict(tag='raw-ax2-binary',path=str(source),destination=str(native/'NNI_ProofDriver'),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),bytes=source.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(files=rows,admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())
raw=json.dumps(x).encode();(b/'NNI_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NNI_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
print(json.dumps(dict(files=len(rows),disk=x['disk'])))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nseeds='+repr(seeds)+'\n'+code,text=True,capture_output=True)
 (E/f'NNI_seed-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode in [78,255,79] and retry<10:
  with (E/'NNI_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(event='wait',stage='seed',exit=r.returncode,retry=retry))+'\n')
  time.sleep(180 if r.returncode==78 else 60 if r.returncode==255 else 30);continue
 raise RuntimeError(r.stdout[-1000:]+r.stderr)
for n in ['NNI_CACHE_IMPORTS.json.xz','NNI_CACHE_IMPORTS.json.sha256']:
 r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
print('seed copied and pinned')
