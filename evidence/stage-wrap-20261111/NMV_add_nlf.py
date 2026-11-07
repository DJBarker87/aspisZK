from NMV_transport import *
import base64
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib,lzma,base64
b=Path({B!r});src=b.parent/'codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014';rows=[]
assert src.is_dir()
for p in src.rglob('*'):
 if p.is_file():
  q=b/'NMV_seed/NLF'/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
(E/'NMV_NLF_IMPORTS.json').write_text(r.stdout)
env=json.loads((E/'NMV_ENV.json').read_text());env['LEAN_PATH']=B+'/NMV_seed/NLF:'+env['LEAN_PATH'];(E/'NMV_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
