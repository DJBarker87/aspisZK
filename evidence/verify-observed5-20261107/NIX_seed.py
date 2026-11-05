from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104')
P=C/'NIH_seed_20261107/NIH_exports_20261107'
D=C/'NIX_seed_20261107/NIH_exports_20261107'
assert not D.exists()
shutil.copytree(P,D)
pins=[dict(path=str(p),source=str(P/p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(D.rglob('*')) if p.is_file()]
paths=json.loads((B/'NIX_PATHS.json').read_text());paths=[str(D) if x==str(P) else x for x in paths];paths.insert(0,str(B/'NIX_objects'))
(B/'NIX_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
Q=Path('/home/dombarker/project-offloads/codex-cx-verify-observed4-20261107')
names=['NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256','NHR_STAGING_MANIFEST.json']
inputs={}
for n in names:
 p=Q/n;shutil.copyfile(p,B/n);inputs[n]=dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
(B/'NIX_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins),inputs=inputs,cargo_target_dir=str(B/'NIX_target')),indent=2)+'\n')
print('NIX retained seed bytes',sum(p['bytes'] for p in pins))
