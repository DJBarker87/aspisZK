from pathlib import Path
import json,hashlib,shutil,os
B=Path(__file__).resolve().parent
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJM_exports_20261108');assert not D.exists();D.mkdir(parents=True)
mods=[r['module'] for r in json.loads((B/'NJM_MODULES.json').read_text())]+['NJM_COMBINED_IMPORT'];files=[]
for m in sorted(set(mods)):
 src=B/'NJM_objects'/(m+'.olean');assert src.is_file(),m
 for p in [src,Path(str(src)+'.private'),Path(str(src)+'.server'),src.with_suffix('.ir')]:
  if p.is_file():
   dst=D/p.name;shutil.copyfile(p,dst);h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
   files.append(dict(module=m,source=str(p),path=str(dst),bytes=p.stat().st_size,sha256=h))
paths=json.loads((B/'NJM_PATHS.json').read_text());paths=[str(D)]+[p for p in paths if p!=str(B/'NJM_objects')]
(B/'NJM_CONSUMER_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
(B/'NJM_EXPORT.json').write_text(json.dumps(dict(path=str(D),total_bytes=sum(r['bytes'] for r in files),files=files),indent=2)+'\n')
# Pin exactly what the standalone loader resolved; no shared object is modified.
search=json.loads((B/'NJM_PATHS.json').read_text());rows=[]
for line in (B/'NJM_LOADED_scan.jsonl').read_text().splitlines():
 n=json.loads(line)['module'];rel=n.replace('.','/')+'.olean';p=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None);assert p is not None,n
 parts=[]
 for suffix,q in [('',p),('.private',Path(str(p)+'.private')),('.server',Path(str(p)+'.server')),('ir',p.with_suffix('.ir'))]:
  if q.is_file():parts.append([suffix,q.stat().st_size,hashlib.sha256(q.read_bytes()).hexdigest()])
 rows.append(dict(module=n,path=str(p),parts=parts))
(B/'NJM_RESOLVED_OBJECTS.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')

for m in mods:
 src=B/'NJM_generated'/(m+'.lean')
 assert src.is_file(),m
 dst=D/(m+'.lean');shutil.copyfile(src,dst)
 files.append(dict(module=m,source=str(src),path=str(dst),bytes=src.stat().st_size,sha256=hashlib.sha256(src.read_bytes()).hexdigest()))
(B/'NJM_EXPORT.json').write_text(json.dumps(dict(path=str(D),total_bytes=sum(r['bytes'] for r in files),files=files),indent=2)+'\n')
print(json.dumps(dict(export_bytes=sum(r['bytes'] for r in files),resolved_modules=len(rows),cache_retained=True)))
