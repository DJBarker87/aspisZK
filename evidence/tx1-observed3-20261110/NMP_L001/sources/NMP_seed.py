from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for tag in ['NLZ','NLR','NLX']:
 x=json.loads((B/('NMP_'+tag+'_EXPORT.json')).read_text());root=Path(x['export'])
 for r in x['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'],str(p)
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  q=B/'NMP_seed'/tag/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  assert sha(p)==sha(q)
  rows.append(dict(source=str(p),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NMP_SEED_PINS.json').write_text(json.dumps(dict(files=rows,bytes=sum(r['bytes'] for r in rows)),indent=1))
print('NLZ first, NLR second, NLX third: copied exports verified')
