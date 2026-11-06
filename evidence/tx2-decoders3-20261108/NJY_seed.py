from NJY_transport import *
admission('NJY_P001')
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib,os
b=Path({B!r});src=Path('/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107')
out=[]
for root,dest in [(src/'NJQ_exports_20261108',b/'NJY_NJQ_seed'),(Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJW_20261108/NJW_exports_20261108'),b/'NJY_NJW_seed')]:
 assert root.is_dir(),str(root)
 dest.mkdir(exist_ok=True);pins=[]
 for p in sorted(root.rglob('*')):
  if p.is_file():
   q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();shutil.copy2(p,q)
   pins.append(dict(relative=str(p.relative_to(root)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 out.append(dict(source=str(root),destination=str(dest),bytes=sum(p['bytes'] for p in pins),pins=pins))
for name in ['S2W_run_host.py','lakefile.lean']:shutil.copy2(src/name,b/name)
(b/'NJY_objects').mkdir(exist_ok=True)
print(json.dumps(dict(seeds=out,free_bytes=shutil.disk_usage(b).free)))
''');assert r.returncode==0,r.stderr
(E/'NJY_SEED.json').write_text(r.stdout)
print(json.dumps({x['destination']:x['bytes'] for x in json.loads(r.stdout)['seeds']}))
