from NMS_transport import *
import base64
admission('NMS_S001')
r=ssh('python3',f'''from pathlib import Path
import json,shutil,hashlib,base64,lzma
b=Path({B!r});rows=[]
for label,source in [('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110'),('NMN','codex-cx-tx2-entry5-20261110/NMN_exports_20261110')]:
 src=b.parent/source
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=b/'NMS_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert p.read_bytes()==q.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['NMS_objects','NMS_generated','NMS_tmp','NMS_target']:(b/n).mkdir(exist_ok=True)
src=b.parent/'codex-cx-tx2-entry5-20261110/S2W_run_host.py';shutil.copy2(src,b/'S2W_run_host.py')
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode(),launcher_sha256=hashlib.sha256(src.read_bytes()).hexdigest())))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NMS_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NMS_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
env=json.loads((E/'NMS_ENV.json').read_text());env['LEAN_PATH']=':'.join([B+'/NMS_objects',B+'/NMS_seed/NLX',B+'/NMS_seed/NMN',env['LEAN_PATH']]);(E/'NMS_ENV.json').write_text(json.dumps(env,indent=1))
