from pathlib import Path
import hashlib,json,shutil
B=Path.cwd(); out=[]
for name,root in [('NJO','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJO_20261108/NJO_exports_20261108'),('NJE','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJE_20261107/NJE_exports_20261107')]:
 src=Path(root); assert src.is_dir(),root
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=B/'NJS_seed'/name/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  out.append(dict(source=str(p),destination=str(q),bytes=p.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
(B/'NJS_objects').mkdir(exist_ok=True);(B/'NJS_target').mkdir(exist_ok=True)
(B/'NJS_SEED.json').write_text(json.dumps(dict(files=out,bytes=sum(x['bytes'] for x in out)),indent=2)+'\n')
(B/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage njs\n')
print(json.dumps(dict(seed_files=len(out),seed_bytes=sum(x['bytes'] for x in out),free_bytes=shutil.disk_usage(B).free)))
