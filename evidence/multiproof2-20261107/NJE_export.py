"""Retain only selected successful own objects; I/O only, never remove cache data."""
from pathlib import Path
import json,hashlib,shutil,os,resource,time
start=time.monotonic();work=Path('/home/dombarker/project-offloads/codex-cx-multiproof2-20261107');dest=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJE_20261107/NJE_exports_20261107');dest.mkdir(parents=True,exist_ok=True)
selected=json.load(open(work/'NJE_SELECTED_MODULES.json'));modules=sorted(selected['dependency_closure'])+['NJE_COMBINED_IMPORT'];files=[]
for module in modules:
 sources=sorted((work/'NJE_objects').glob(module+'.*'));assert any(p.name==module+'.olean' for p in sources),module
 for source in sources:
  if not source.is_file():continue
  digest=hashlib.sha256(source.read_bytes()).hexdigest();target=dest/source.name
  if target.exists():assert hashlib.sha256(target.read_bytes()).hexdigest()==digest,str(target)
  else:shutil.copy2(source,target)
  assert hashlib.sha256(target.read_bytes()).hexdigest()==digest
  files.append(dict(module=module,source=str(source),path=str(target),sha256=digest,bytes=source.stat().st_size))
manifest=dict(path=str(dest),modules=modules,files=files,bytes=sum(x['bytes'] for x in files),wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,action='I/O-only retention of selected objects, not a build; never deletes existing cache',target_established=False)
(work/'NJE_EXPORT.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(files=len(files),bytes=manifest['bytes'],path=str(dest))))
