"""Copy just the recorded Aeneas import closure; no build and no hardlinks."""
from pathlib import Path
import subprocess,json,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';x=json.loads(lzma.decompress((E/'PCI_ACCEPTED_CLOSURE.json.xz').read_bytes()));payload=base64.b64encode(lzma.compress(json.dumps(x).encode())).decode()
code='''from pathlib import Path
import json,subprocess,shutil,hashlib,lzma,base64,sys
B=Path('/home/dombarker/project-offloads/codex-pc-deposit-children2-20261110');C=B.parent/'codex-pc-deposit-children2-cache-20261110'
with (B/'PCI_ACCEPTED_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3',str(B.parent/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'PCI_ACCEPTED_SEED-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'PCI_ACCEPTED_SEED-reservation.json';a=json.loads(p.read_text()) if p.exists() else None
if r.returncode!=0 or not a or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=a)));sys.exit(r.returncode or 78)
assert shutil.disk_usage(B).free>=40_000_000_000
imports=json.loads(lzma.decompress((B/'PCI_IMPORTS.json.xz').read_bytes()));x=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)))
for v in x['files']:
 p=Path(v['path']);stem=v['module'].replace('.','/');tail=str(p).split(stem+'.olean',1);rel=stem+'.olean'+tail[1] if len(tail)==2 else stem+'.ir';q=C/rel
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==v['sha256'],str(p)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,rel
 else:q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 imports[rel]=dict(source=str(p),sha256=h,bytes=p.stat().st_size)
(B/'PCI_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(imports).encode()))
print(json.dumps(dict(files=len(imports),bytes=sum(v['bytes'] for v in imports.values()),disk_free=shutil.disk_usage(B).free,admission=a)))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True);(E/'PCI_ACCEPTED_SEED.log').write_text(r.stdout+r.stderr);print('PCI full seed exit',r.returncode,r.stdout[-250:],r.stderr[-500:]);raise SystemExit(r.returncode)
