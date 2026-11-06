from pathlib import Path
import json,hashlib,shutil,os
B=Path(__file__).resolve().parent
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJG_exports_20261107');assert not D.exists();D.mkdir(parents=True)
mods=[r['module'] for r in json.loads((B/'NJG_MODULES.json').read_text())]+['NJG_BASE_IMPORT','NJG_COMBINED_IMPORT','JFw_Validator','JFw_Record'];files=[]
for m in sorted(set(mods)):
 src=B/'NJG_objects'/(m+'.olean');assert src.is_file(),m
 for p in [src,Path(str(src)+'.private'),Path(str(src)+'.server'),src.with_suffix('.ir')]:
  if p.is_file():
   dst=D/p.name;shutil.copyfile(p,dst);h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
   files.append(dict(module=m,source=str(p),path=str(dst),bytes=p.stat().st_size,sha256=h))
paths=json.loads((B/'NJG_PATHS.json').read_text());paths=[str(D)]+[p for p in paths if p!=str(B/'NJG_objects')]
(B/'NJG_CONSUMER_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
(B/'NJG_EXPORT.json').write_text(json.dumps(dict(path=str(D),total_bytes=sum(r['bytes'] for r in files),files=files),indent=2)+'\n')
# Pin exactly what the standalone loader resolved; no shared object is modified.
search=json.loads((B/'NJG_PATHS.json').read_text());rows=[]
for line in (B/'NJG_LOADED_scan.jsonl').read_text().splitlines():
 n=json.loads(line)['module'];rel=n.replace('.','/')+'.olean';p=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None);assert p is not None,n
 parts=[]
 for suffix,q in [('',p),('.private',Path(str(p)+'.private')),('.server',Path(str(p)+'.server')),('ir',p.with_suffix('.ir'))]:
  if q.is_file():parts.append([suffix,q.stat().st_size,hashlib.sha256(q.read_bytes()).hexdigest()])
 rows.append(dict(module=n,path=str(p),parts=parts))
(B/'NJG_RESOLVED_OBJECTS.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
# Clean only attributed rebuildable outputs; preserve the named retained cache and sources.
clean=[]
for name in ['NJG_target','NJG_tmp','NHR_target']:
 p=B/name
 if not p.exists():continue
 candidates=[q for q in p.rglob('*') if q.is_file()]
 possible_keys=[str(q) for q in candidates if q.name.endswith(('-keypair.json','.pem','.key'))]
 if possible_keys:clean.append(dict(path=str(p),status='KEPT',reason='possible key filenames; no key cleanup authorized',files=possible_keys));continue
 count=len(candidates);size=sum(q.stat().st_size for q in candidates);shutil.rmtree(p);clean.append(dict(path=str(p),status='REMOVED_OWN_REBUILDABLE_OUTPUTS',files=count,bytes=size))
stat=shutil.disk_usage(B)
(B/'NJG_HOST_END.json').write_text(json.dumps(dict(export=str(D),export_bytes=sum(r['bytes'] for r in files),resolved_modules=len(rows),cleanup=clean,free_bytes=stat.free,total_bytes=stat.total,cache_deleted=False,keys_touched=False),indent=2)+'\n')
print(json.dumps(dict(export_bytes=sum(r['bytes'] for r in files),resolved_modules=len(rows),free_bytes=stat.free,cache_retained=True)))
