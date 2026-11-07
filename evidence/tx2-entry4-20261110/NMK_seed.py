from NMK_transport import *
import base64
admission('NMK_S001')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,base64,lzma
b=Path({B!r});rows=[]
seeds=[('NLW','codex-cx-tx2-entry3-20261110/NLW_exports_20261110_5a16d2f3c74d'),('NMD','codex-cx-cut-pilot-20261110/NMD_exports_7299666cbf38'),('NMF','codex-cx-root-transport-20261110/NMF_exports_20261110'),('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110')]
for label,source in seeds:
 src=b.parent/source;assert src.is_dir(),str(src)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=b/'NMK_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['NMK_objects','NMK_generated','NMK_tmp','NMK_target']:(b/n).mkdir(exist_ok=True)
shutil.copy2(b.parent/'codex-cx-tx2-entry-20261109/S2W_run_host.py',b/'S2W_run_host.py')
raw=json.dumps(rows).encode();(b/'NMK_SEED.json.xz').write_bytes(lzma.compress(raw));print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NMK_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NMK_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
env=json.loads((E/'NMK_ENV.json').read_text());env['LEAN_PATH']=':'.join([B+'/NMK_objects',*[B+'/NMK_seed/'+n for n in ['NLW','NMD','NMF','NLX']],env['LEAN_PATH']]);(E/'NMK_ENV.json').write_text(json.dumps(env,indent=1))
