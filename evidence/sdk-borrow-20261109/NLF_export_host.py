from pathlib import Path
import json,hashlib,shutil,lzma,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=json.loads((B/'NLF_EXPORT_MODULES.json').read_text())
rows=[]
for m in mods:
 p=B/'NLF_objects'/(m+'.olean');assert p.is_file(),m
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():rows.append(dict(relative=str(q.relative_to(B/'NLF_objects')),sha256=sha(q),bytes=q.stat().st_size))
tree=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest();dest=B/('NLF_exports_20261109_'+tree[:12]);assert not dest.exists();dest.mkdir()
for r in rows:shutil.copy2(B/'NLF_objects'/r['relative'],dest/r['relative'])
for r in rows:assert sha(dest/r['relative'])==r['sha256']
(B/'NLF_EXPORT.json').write_text(json.dumps(dict(export=str(dest),tree_sha256=tree,bytes=sum(r['bytes'] for r in rows),files=rows),indent=1)+'\n')
scan=[json.loads(l) for l in (B/'NLF_LOADED_scan.jsonl').read_text().splitlines()]
roots=os.environ['LEAN_PATH'].split(':')+[os.environ['LEAN_SYSROOT']+'/lib/lean'];pins=[]
for row in scan:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,objects=pins),indent=1).encode();(B/'NLF_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NLF_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NLF_HOST_FINAL.json').write_text(json.dumps(dict(free_bytes=shutil.disk_usage(B).free,own_bytes=sum(p.stat().st_size for p in B.rglob('*') if p.is_file() and not p.is_symlink()),export=str(dest),export_bytes=sum(r['bytes'] for r in rows),pinned_objects=len(pins),no_key_operations=True,CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR']),indent=1)+'\n')
print('NLF exported own objects and pinned the complete selected closure; no shared/cache writes')
