from NMV_formal import *
import base64
admission('NMV_E002_upload')
files={n:base64.b64encode((E/n).read_bytes()).decode() for n in ['NMV_FROZEN_PAYLOAD.json.xz','NMV_FROZEN_PAYLOAD.json.sha256','NMV_STAGING_MANIFEST.json']}
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r})
for n,v in json.loads({json.dumps(files)!r}).items():(b/n).write_bytes(base64.b64decode(v))
''');assert r.returncode==0,r.stderr
files={n:(E/n).read_text() for n in ['NMV_stage.py','NMV_OPACITY.json']}
r=run('NMV_L002','extract','snapshot',['python3','NMV_stage.py','--extract','--function','snapshot','--workspace',B+'/NMV_src','--out',B+'/NMV_extracted/snapshot','--opacity',B+'/NMV_OPACITY.json'],files,{'CARGO_TARGET_DIR':B+'/NMV_NHR_target','CARGO_NET_OFFLINE':'true','RUSTFLAGS':''})
r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64
b=Path({B!r});print(json.dumps({{str(p.relative_to(b)):base64.b64encode(lzma.compress(p.read_bytes())).decode() for p in (b/'NMV_extracted').rglob('*') if p.is_file()}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 raw=lzma.decompress(base64.b64decode(t));p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if len(raw)>20_000_000:p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
