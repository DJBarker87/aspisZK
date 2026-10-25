#!/usr/bin/env python3
"""No Lean invocation: complete namespace layout and pin every reused object."""
import pathlib,json,hashlib,os
B=pathlib.Path(__file__).resolve().parent; r=json.loads((B/'input-pins.json').read_text());O=B/'dependency-objects'; paths=r['lean_path'].split(':');items=[]
for m in r['modules']:
 key=m['name'].replace('.','/')+'.olean';p=O/key
 if not p.is_file():
  original=next((pathlib.Path(d)/key for d in paths if (pathlib.Path(d)/key).is_file()),None)
  assert original is not None,m['name']
  assert hashlib.sha256(original.read_bytes()).hexdigest()==m['sha256'],m['name']
  p.parent.mkdir(parents=True,exist_ok=True)
  if p.is_symlink():p.unlink()
  p.symlink_to(original)
  for suffix in ['.server','.private']:
   src=pathlib.Path(str(original)+suffix);dest=pathlib.Path(str(p)+suffix)
   if src.exists() and not dest.exists():dest.symlink_to(src)
  src=original.with_suffix('.ir');dest=p.with_suffix('.ir')
  if src.exists() and not dest.exists():dest.symlink_to(src)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256'],m['name']
 items.append({'name':m['name'],'sha256':m['sha256'],'path':str(p),'imports':m['imports']})
s=json.loads((B/'dependency-object-snapshot.json').read_text())
for m in s['objects']:
 p=O/m['file'];assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256'],str(p)
# Only directories/copies owned by this job; do not chmod symlink targets.
for root,dirs,files in os.walk(O):
 for f in files:
  p=pathlib.Path(root)/f
  if not p.is_symlink():p.chmod(0o444)
 pathlib.Path(root).chmod(0o555)
output=json.dumps(items,sort_keys=True).encode();(B/'frozen-full-objects.json').write_bytes(output)
print(json.dumps({'verified_modules':len(items),'verified_snapshot_files':len(s['objects']),'full_manifest_sha256':hashlib.sha256(output).hexdigest(),'full_manifest_bytes':len(output),'layout':'complete module namespaces; job-owned copies and hash-checked external cache symlinks','all_match':True}))
