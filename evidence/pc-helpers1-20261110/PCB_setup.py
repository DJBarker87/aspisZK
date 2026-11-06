"""Own read-only seed client. Does not launch a Lean/Rust/Kani scope."""
from pathlib import Path
import subprocess,json,lzma,base64,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
x=json.loads(lzma.decompress((E.parent/'ledger21-20261110/NLG_CLOSURE_PINS.json.xz').read_bytes()))
payload=base64.b64encode(lzma.compress(json.dumps(x).encode())).decode()
code='''from pathlib import Path
import json,subprocess,shutil,hashlib,lzma,base64,sys
B=Path('/home/dombarker/project-offloads/codex-pc-helpers1-20261110');C=Path('/home/dombarker/project-offloads/codex-pc-helpers1-cache-20261110');W=B.parent/'codex-cx-sound-int2-20261025'
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
with (B/'PCB_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3',str(B.parent/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'PCB_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'PCB_SETUP-reservation.json';a=json.loads(p.read_text()) if p.exists() else None
if r.returncode!=0 or not a or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=a)));sys.exit(r.returncode or 78)
assert shutil.disk_usage(B).free>=40_000_000_000,'disk below40GB'
x=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)));imports={}
for v in x['selected_objects']:
 p=Path(v['path']);suffix=str(p).split(v['module'].replace('.','/')+'.olean',1)
 if len(suffix)!=2:
  # ir sidecars use the module stem plus .ir
  rel=v['module'].replace('.','/')+'.ir'
 else:rel=v['module'].replace('.','/')+'.olean'+suffix[1]
 q=C/rel;h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==v['sha256'],str(p)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,rel
 else:q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 imports[rel]=dict(source=str(p),sha256=h,bytes=p.stat().st_size)
for sub in ['PCB_generated','PCB_objects','PCB_tmp','PCB_native']:(B/sub).mkdir(exist_ok=True)
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:shutil.copyfile(W/n,B/n)
(B/'PCB_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(imports).encode()))
print(json.dumps(dict(exit=0,admission=a,files=len(imports),bytes=sum(v['bytes'] for v in imports.values()),manifest_sha256=hashlib.sha256((B/'PCB_IMPORTS.json.xz').read_bytes()).hexdigest(),disk_free=shutil.disk_usage(B).free)))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
(E/'PCB_SETUP.log').write_text(r.stdout+r.stderr)
print('PCB seed exit',r.returncode, r.stdout[-1200:],r.stderr[-300:])
raise SystemExit(r.returncode)
