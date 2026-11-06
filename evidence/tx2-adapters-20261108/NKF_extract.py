from NKF_formal import *
import base64
files={n:(E/n).read_text() for n in ['NKF_stage.py','NKF_OPACITY.json']}
# Retained immutable payload and manifest, already copied once during seed.
r=ssh('python3',f'''from pathlib import Path
import shutil
b=Path({B!r});src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry7-20261107')
for n in ['NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256','NHR_STAGING_MANIFEST.json']:shutil.copy2(src/n,b/n)
''');assert r.returncode==0,r.stderr
r=run('NKF_L002','extraction','six actual frozen adapter leaves',['python3','NKF_stage.py','--extract','--function','entry','--workspace','NKF_src','--out','NKF_EMITTED','--opacity','NKF_OPACITY.json'],files)
r2=ssh('python3',f'''from pathlib import Path
import json,base64,lzma
b=Path({B!r});print(json.dumps({{str(p.relative_to(b)):base64.b64encode(lzma.compress(p.read_bytes())).decode() for p in (b/'NKF_EMITTED').rglob('*') if p.is_file()}}))
''');assert r2.returncode==0,r2.stderr
for n,v in json.loads(r2.stdout).items():
 raw=lzma.decompress(base64.b64decode(v));p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if len(raw)>20*1024*1024:p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
print('NKF extraction terminal exit='+str(r['exit_status']))
