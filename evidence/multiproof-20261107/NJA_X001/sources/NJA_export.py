"""Retain selected compiled objects; never remove or overwrite a shared cache."""
from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJA_20261107/NJA_exports_20261107')
selected=json.loads((B/'NJA_SELECTED_MODULES.json').read_text());files=[]
for m,info in selected.items():
 stem=m.replace('.','/');source=B/info['source'];assert source.is_file()
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  src=B/'NJA_objects'/(stem+suffix)
  if not src.exists():
   assert suffix!='.olean',src
   continue
  sha=hashlib.sha256(src.read_bytes()).hexdigest();dst=C/(stem+suffix);dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==sha
  else:shutil.copy2(src,dst)
  files.append({'path':str(dst),'sha256':sha,'bytes':dst.stat().st_size,'module':m,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()})
x={'cache':str(C),'files':files,'exported_bytes':sum(f['bytes'] for f in files),'selected_modules':len(selected),'seed':'NJA_SEED.json','retained_workspace':str(B),'cargo_target_dirs':[str(B/'NJA_target'),str(B/'NHR_target')],'disk':dict(zip(['total','used','free'],shutil.disk_usage(B))),'deletions':[]}
(B/'NJA_EXPORT.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({'exported_files':len(files),'exported_bytes':x['exported_bytes'],'disk_free':x['disk']['free']}))
