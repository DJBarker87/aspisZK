"""Pin the selected coherent objects and retain a copy-only Lean export."""
from pathlib import Path
import os,json,hashlib,subprocess,lzma,shutil,time
B=Path.cwd();start=time.monotonic()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
T=Path(os.environ['LEAN_SYSROOT'])
paths=subprocess.check_output([str(T/'bin/lake'),'env','printenv','LEAN_PATH'],text=True).strip().split(':')
paths=[str((B/p).resolve())if not Path(p).is_absolute()else p for p in paths if p]+[str(T/'lib/lean')]
modules=json.loads((B/'LIB_SELECTED_MODULES.json').read_text());selected=[];objects=[]
for name in modules:
 rel=name.replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if (Path(root)/rel).is_file()),None)
 assert p is not None,name
 selected.append(dict(module=name,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():objects.append(dict(module=name,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
for row in json.loads((B/'LIB_FINAL_SOURCE_PINS.json').read_text()):
 p=B/'LIB_generated'/(row['module'].replace('.','/')+'.lean');assert p.exists() and sha(p)==row['sha256'],row['module']
raw=json.dumps(dict(selected_modules=selected,objects=objects,lean_path=paths),separators=(',',':')).encode()
(B/'LIB_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6))
(B/'LIB_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
export=B/'LIB_exports_A_20261111';export.mkdir(exist_ok=True);files=[]
for row in objects:
 p=Path(row['path'])
 if not p.is_relative_to(B/'LIB_objects'):continue
 if not (row['module'].startswith('LIB_') or row['module'].startswith('RSL_')):continue
 q=export/p.relative_to(B/'LIB_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==row['sha256'],'Existing own export differs: '+str(q)
 else:shutil.copy2(p,q)
 assert sha(q)==row['sha256']
 files.append(dict(path=str(q),sha256=row['sha256'],bytes=q.stat().st_size,module=row['module']))
(B/'LIB_EXPORT.json').write_text(json.dumps(dict(export=str(export),files=files,copy_only=True,retained=True),indent=2)+'\n')
summary=dict(selected_modules=len(selected),object_files=len(objects),export_files=len(files),closure_sha256=hashlib.sha256(raw).hexdigest(),closure_bytes=len(raw),free=shutil.disk_usage(B).free,wall_seconds=time.monotonic()-start,caches_deleted=False)
(B/'LIB_FINAL_HOST.json').write_text(json.dumps(summary,indent=2)+'\n')
E=B/'LIB_audit/pins';E.mkdir(parents=True,exist_ok=True);(E/'pins.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
