from NKF_transport import *
import base64,lzma,hashlib
admission('NKF_P002')
r=ssh('python3',f'''from pathlib import Path
import json,shutil,hashlib,base64
b=Path({B!r});src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry7-20261107');dst=b/'NKF_src';assert not dst.exists()
shutil.copytree(src/'NIV_src',dst,ignore=shutil.ignore_patterns('target','__pycache__'))
pins=[]
for p in dst.rglob('*'):
 if p.is_file():pins.append(dict(relative=str(p.relative_to(dst)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:
 shutil.copy2(Path('/home/dombarker/project-offloads/codex-cx-tx2-decoders3-20261107/NIJ_src')/n,dst/n)
print(json.dumps(dict(source=str(src/'NIV_src'),destination=str(dst),bytes=sum(x['bytes'] for x in pins),pins=pins,free_bytes=shutil.disk_usage(b).free,inputs={{n:base64.b64encode((src/n).read_bytes()).decode() for n in ['NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256','NHR_STAGING_MANIFEST.json']}})))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout)
for n,v in x.pop('inputs').items():(E/('NKF_'+n)).write_bytes(base64.b64decode(v))
(E/'NKF_RUST_SEED.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='pins'}))
