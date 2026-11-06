"""Retain only current semantic objects, their source hashes and complete sidecars."""
from NLK_formal import *
mods=json.loads((E/'NLK_SEMANTIC_MODULES.json').read_text())+['NLK_COMBINED_IMPORT']
script='''from pathlib import Path
import json,hashlib,shutil
b=Path.cwd();mods=json.loads((b/'NLK_EXPORT_MODULES.json').read_text());dest=b/'NLK_exports_20261110_256baac6480';dest.mkdir(exist_ok=True);rows=[]
for mod in mods:
 p=b/'NLK_objects'/(mod+'.olean');assert p.exists(),mod
 for f in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not f.exists():continue
  raw=f.read_bytes();h=hashlib.sha256(raw).hexdigest();q=dest/f.name
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,q
  else:q.write_bytes(raw)
  rows.append(dict(module=mod,path=str(q),sha256=h,bytes=len(raw)))
 src=b/'NLK_generated'/(mod+'.lean');raw=src.read_bytes();(dest/src.name).write_bytes(raw)
 rows.append(dict(module=mod,path=str(dest/src.name),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),source=True))
size=sum(p.stat().st_size for p in b.rglob('*') if p.is_file() and not p.is_symlink());assert size<30_000_000_000,size
out=dict(path=str(dest),files=rows,bytes=sum(r['bytes'] for r in rows),workspace_bytes=size,free_bytes=shutil.disk_usage(b).free,closure_pins_sha256=hashlib.sha256((b/'NLK_CLOSURE_PINS.json').read_bytes()).hexdigest(),source_stage_commit='256baac6480ddac8119b09ae6696cc64594e7239',CARGO_TARGET_DIR=str(b/'NLK_target'),cache_retained=True)
(b/'NLK_EXPORT.json').write_text(json.dumps(out,indent=1)+'\\n');print(json.dumps({k:out[k] for k in ['path','bytes','workspace_bytes','free_bytes']}))
'''
r=run('NLK_L094','cache','NLK_FinalExport',['python3','NLK_export_host.py'],extra={'NLK_export_host.py':script,'NLK_EXPORT_MODULES.json':json.dumps(mods)});assert r['exit_status']==0
r=ssh('python3',f"from pathlib import Path;print(Path({B!r},'NLK_EXPORT.json').read_text())");assert r.returncode==0
(E/'NLK_EXPORT.json').write_text(r.stdout)
print('Retained current semantic sources, objects and sidecars; private cache and target kept')
