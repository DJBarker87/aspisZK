from pathlib import Path
import shutil,json,hashlib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-verify-observed3-20261106');C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104');D=C/'NIH_seed_20261107'
assert not (B/'NIH_src').exists()
shutil.copytree(P/'NHU_src',B/'NIH_src')
# Copy retained exports once; no sibling workspace is written.
exports=[C/'NHU_seed_20261106/NHU_exports_20261106',C/'NHU_seed_20261106/NHG_exports_20261106',C/'NHG_seed_20261106/NGX_imported_20261106',C/'NHG_seed_20261106/NGK_imported_20261106']
pins=[]
for source in exports:
 dest=D/source.name;shutil.copytree(source,dest)
 for p in sorted(dest.rglob('*')):
  if p.is_file():pins.append(dict(path=str(p),source=str(source/p.relative_to(dest)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
paths=json.loads((B/'NIH_PRIOR_PATHS.json').read_text())
for source in exports:paths=[str(D/source.name) if p==str(source) else p for p in paths]
paths.insert(0,str(B/'NIH_objects'))
(B/'NIH_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
(B/'NIH_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins),scratch_bytes=sum(p.stat().st_size for p in (B/'NIH_src').rglob('*') if p.is_file())),indent=2)+'\n')
print('seed bytes',sum(p['bytes'] for p in pins))
