from pathlib import Path
import json,lzma,hashlib,shutil
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for tag,manifest in [('NLR','NLZ_NLR_EXPORT.json'),('NLS','NLZ_LEDGER23_EXPORT.json')]:
 x=json.loads((B/manifest).read_text());root=Path(x['export'])
 for r in x['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'],str(p)
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  q=B/'NLZ_seed'/tag/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  assert sha(p)==sha(q)
  rows.append(dict(source=str(p),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
x=json.loads(lzma.decompress((B/'NLZ_NLR_CLOSURE_PINS.json.xz').read_bytes()))
for r in x['selected_objects']:assert sha(Path(r['path']))==r['sha256'],r['path']
(B/'NLZ_SEED_PINS.json').write_text(json.dumps(dict(files=rows,closure_objects_verified=len(x['selected_objects']),closure_manifest_sha256=sha(B/'NLZ_NLR_CLOSURE_PINS.json.xz'),bytes=sum(r['bytes'] for r in rows)),indent=2))
print('NLR first, NLS second; exports copied and NLR closure hashes verified')
