from pathlib import Path
import shutil,json,hashlib,subprocess
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Ordered first two immutable seeds; no hard links and no writes to source roots.
roots=[('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKH_20261108/NKH_exports_20261108','NKJ_seed/NKH'),('/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104/NGH_exports_20261105','NKJ_seed/NGH')]
pins=[]
for origin,dest in roots:
 for p in sorted(Path(origin).rglob('*')):
  if p.is_file():
   q=B/dest/p.relative_to(origin);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
   assert sha(p)==sha(q);pins.append(dict(origin=str(p),copy=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NKJ_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(x['bytes'] for x in pins)),indent=2))
# Retained predecessor source-only extraction scratch, excluding all build output.
shutil.copytree('/home/dombarker/project-offloads/codex-cx-aeneas-loops-20261105/NHA_scratch',B/'NKJ_src',ignore=shutil.ignore_patterns('target','.git','__pycache__'),dirs_exist_ok=False)
for d in ['NKJ_objects','NKJ_tmp','NKJ_bin','NKJ_inputs','NKJ_raw']:(B/d).mkdir(exist_ok=True)
for n in ['charon','charon-driver','aeneas-b59d5188-extended']:
 p=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')/n
 shutil.copy2(p,B/'NKJ_bin'/n)
(B/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage nkj\n')
print('NKJ source scratch and ordered seeds copied')
