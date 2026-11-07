from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();sha=lambda raw:hashlib.sha256(raw).hexdigest()
x=json.loads((B/'NMM_EXPORT_CONFIG.json').read_text());dest=B/x['directory'];dest.mkdir(exist_ok=True);rows=[]
for mod in x['modules']:
 p=B/'NMM_objects'/(mod+'.olean');assert p.is_file(),mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir'),B/'NMM_generated'/(mod+'.lean')]:
  if not z.is_file():continue
  raw=z.read_bytes();q=dest/z.name
  if q.exists():assert sha(q.read_bytes())==sha(raw),str(q)
  else:q.write_bytes(raw)
  rows.append(dict(module=mod,path=str(q),sha256=sha(raw),bytes=len(raw),source=z.suffix=='.lean'))
size=sum(p.stat().st_size for p in B.rglob('*') if p.is_file() and not p.is_symlink());assert size<30_000_000_000,size
out=dict(path=str(dest),files=rows,bytes=sum(r['bytes'] for r in rows),workspace_bytes=size,free_bytes=shutil.disk_usage(B).free,source_stage_commit=x['source_stage_commit'],CARGO_TARGET_DIR=str(B/'NMM_target'),cache_retained=True,TMPDIR_retained=True,scope='Checked support objects only; no candidate roots',closure_pins_sha256=sha((B/'NMM_CLOSURE_PINS.json').read_bytes()))
(B/'NMM_EXPORT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps({k:out[k] for k in ['path','bytes','workspace_bytes','free_bytes']}))
