from pathlib import Path
import shutil,hashlib,json
B=Path(__file__).resolve().parent
rows=[]
for tag in ['NMC','NLU','NLX']:
 x=json.loads((B/('NMO_'+tag+'_EXPORT_INPUT.json')).read_text())
 for r in x['files']:
  p=Path(r['path']);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==r['sha256'],str(p)
  rel=p.relative_to(x['export']);q=B/'NMO_seed'/tag/rel;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
(B/'NMO_SEED_PINS.json').write_text(json.dumps(dict(files=rows,bytes=sum(r['bytes'] for r in rows)),indent=2))
print(json.dumps(dict(files=len(rows),bytes=sum(r['bytes'] for r in rows))))
