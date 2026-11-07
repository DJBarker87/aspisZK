"""Own setup: copy only selected immutable inputs, never launch a prover."""
from pathlib import Path
import subprocess,json,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
x=json.loads(lzma.decompress((E.parent/'ledger23-20261110/NLS_CLOSURE_PINS.json.xz').read_bytes()))
payload=base64.b64encode(lzma.compress(json.dumps(x).encode())).decode()
code='''from pathlib import Path
import json,subprocess,shutil,hashlib,lzma,base64,sys
B=Path('/home/dombarker/project-offloads/codex-pc-deposit-children1-20261110');C=Path('/home/dombarker/project-offloads/codex-pc-deposit-children1-cache-20261110');W=B.parent/'codex-cx-sound-int2-20261025'
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
with (B/'PCF_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3',str(B.parent/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'PCF_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'PCF_SETUP-reservation.json';a=json.loads(p.read_text()) if p.exists() else None
if r.returncode!=0 or not a or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=a)));sys.exit(r.returncode or 78)
assert shutil.disk_usage(B).free>=40_000_000_000,'disk below40GB'
x=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)));imports={}
# First focused module needs Init only. Broader imports are added on demand.
for v in x['selected_objects']:
 if not(v['module']=='Init' or v['module'].startswith('Init.')):continue
 p=Path(v['path']);stem=v['module'].replace('.','/');tail=str(p).split(stem+'.olean',1)
 rel=stem+'.olean'+tail[1] if len(tail)==2 else stem+'.ir'
 q=C/rel;h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==v['sha256'],str(p)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,rel
 else:q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 imports[rel]=dict(source=str(p),sha256=h,bytes=p.stat().st_size)
for sub in ['PCF_generated','PCF_objects','PCF_tmp','PCF_native']:(B/sub).mkdir(exist_ok=True)
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:shutil.copyfile(W/n,B/n)
(B/'PCF_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(imports).encode()))
print(json.dumps(dict(exit=0,admission=a,files=len(imports),bytes=sum(v['bytes'] for v in imports.values()),manifest_sha256=hashlib.sha256((B/'PCF_IMPORTS.json.xz').read_bytes()).hexdigest(),disk_free=shutil.disk_usage(B).free)))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
(E/'PCF_SETUP.log').write_text(r.stdout+r.stderr)
print('PCF seed exit',r.returncode,r.stdout[-1400:],r.stderr[-300:])
raise SystemExit(r.returncode)
