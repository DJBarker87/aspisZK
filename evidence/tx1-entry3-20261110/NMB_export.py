"""COPY own checked objects into a retained export; never hardlink/mutate seeds."""
from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();plan=json.loads((B/'NMB_AUDIT_PLAN.json').read_text());out=B/'NMB_exports_20261110';out.mkdir(exist_ok=True)
def sha(p):
 with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
modules=plan['modules']+['NMB_COMBINED_IMPORT'];files=[]
for m in modules:
 stem=B/'NMB_objects'/m.replace('.','/');source=B/'NMB_generated'/(m.replace('.','/')+'.lean');assert source.is_file()
 assert stem.with_suffix('.olean').is_file()
 for p in [stem.with_suffix('.olean'),Path(str(stem)+'.olean.private'),Path(str(stem)+'.olean.server'),stem.with_suffix('.ir')]:
  if p.is_file():
   rel=p.relative_to(B/'NMB_objects');q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
   if q.exists():assert sha(q)==sha(p)
   else:shutil.copy2(p,q)
   assert sha(q)==sha(p);files.append(dict(relative=str(rel),path=str(q),sha256=sha(q),bytes=q.stat().st_size,source_sha256=sha(source),module=m))
manifest=dict(export=str(out),method='copy2; no hardlinks',modules=modules,files=files,bytes=sum(x['bytes']for x in files),target_established=False,roots=[],credit='source-support only',retained=True,deleted_files=0)
(B/'NMB_EXPORT.json').write_text(json.dumps(manifest,indent=1)+'\n');print(json.dumps(dict(export=str(out),modules=len(modules),bytes=manifest['bytes'])))
