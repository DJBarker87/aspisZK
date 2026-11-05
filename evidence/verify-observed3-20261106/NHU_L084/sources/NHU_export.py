from pathlib import Path
import shutil,hashlib,json
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NHU_seed_20261106');dest=C/'NHU_exports_20261106'
assert not dest.exists(),'Never overwrite a retained export'
dest.mkdir();mods=[r['module'] for r in json.loads((B/'NHU_MODULES.json').read_text())]+['NHU_COMBINED_IMPORT'];rows=[]
for module in mods:
 p=B/'NHU_objects'/(module+'.olean');assert p.is_file(),module
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if src.is_file():
   out=dest/src.name;shutil.copy2(src,out);raw=src.read_bytes();sha=hashlib.sha256(raw).hexdigest();assert hashlib.sha256(out.read_bytes()).hexdigest()==sha
   rows.append(dict(module=module,path=str(out),sha256=sha,bytes=len(raw)))
paths=json.loads((B/'NHU_PATHS.json').read_text()) if (B/'NHU_PATHS.json').exists() else None
# The runner pins the exact incoming path list in its config. Do not infer a new one.
config=json.loads((B/'NHU_L084.json').read_text()) if (B/'NHU_L084.json').exists() else None
if config:paths=config['env']['LEAN_PATH'].split(':')
assert paths is not None
closure=[];loaded=[json.loads(l) for l in (B/'NHU_LOADED_scan.jsonl').read_text().splitlines()]
for row in loaded:
 module=row.get('module',row.get('name'));assert module,row
 rel=module.replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if (Path(root)/rel).is_file()),None);assert p is not None,module
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if src.is_file():closure.append(dict(module=module,path=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bytes=src.stat().st_size))
raw=(json.dumps(closure,sort_keys=True)+'\n').encode();(B/'NHU_CLOSURE_PINS.json').write_bytes(raw);(B/'NHU_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
report=dict(status='PASS',export=str(dest),files=rows,bytes=sum(r['bytes'] for r in rows),modules=mods,closure_modules=len(loaded),closure_objects=len(closure),closure_sha256=hashlib.sha256(raw).hexdigest(),cache_deleted=False)
(B/'NHU_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(dict(status='PASS',export=str(dest),bytes=report['bytes'],closure_modules=len(loaded))))
