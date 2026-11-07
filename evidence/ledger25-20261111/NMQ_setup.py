from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111'
seeds=json.loads((E/'NMQ_SEED_INPUTS.json').read_text())
closure_inputs=[]
for folder,pre in [(E.parent/'ledger24-20261110','NLX'),(E.parent/'tx2-entry5-20261110','NMN'),(E.parent/'root-transport-20261110','NMF')]:
 p=folder/(pre+'_CLOSURE_PINS.json.xz');sha=(folder/(pre+'_CLOSURE_PINS.json.sha256')).read_text().strip();closure_inputs.append(dict(hex=p.read_bytes().hex(),sha256=sha))
code='''from pathlib import Path
import json,subprocess,sys,hashlib,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NMQ_seed-admission.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NMQ_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NMQ_seed-admission.json'
if not p.exists():sys.exit(79)
a=json.loads(p.read_text())
if r.returncode or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
for receipt in closure_inputs:
 raw=lzma.decompress(bytes.fromhex(receipt['hex']));assert hashlib.sha256(raw).hexdigest()==receipt['sha256']
 data=json.loads(raw)
 for row in (data.get('selected_objects',list(data.values())) if isinstance(data,dict) else data):
  p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
c=Path(C);c.mkdir(exist_ok=True);rows=[]
for row in seeds:
 p=Path(row['path']);assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 q=c/(row['tag']+'_seed')/row['relative'];q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
 rows.append(dict(row,destination=str(q)))
native=b/'NMQ_native';native.mkdir(exist_ok=True)
source=Path('/home/dombarker/project-offloads/codex-cx-ledger24-20261110/NLX_native/NLX_ProofDriver')
shutil.copy2(source,native/'NMQ_ProofDriver')
rows.append(dict(tag='raw-ax2-binary',path=str(source),destination=str(native/'NMQ_ProofDriver'),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),bytes=source.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(files=rows,bytes=sum(Path(r['destination']).stat().st_size for r in rows),admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())
(b/'NMQ_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(dict(files=len(rows),bytes=x['bytes'],disk=x['disk'])))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nseeds='+repr(seeds)+'\nclosure_inputs='+repr(closure_inputs)+'\n'+code,text=True,capture_output=True)
 (E/f'NMQ_seed-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode in[78,255,79]and retry<10:time.sleep(180 if r.returncode==78 else 60 if r.returncode==255 else 30);continue
 raise RuntimeError(r.stdout[-1000:]+r.stderr)
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NMQ_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NMQ_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
print('NLX seed copied and hash checked')
