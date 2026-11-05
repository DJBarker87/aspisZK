from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;store=E/'NGW_INPUTS';store.mkdir(exist_ok=True);rows=[]
for d in sorted(E.glob('NGW_[KLE][0-9][0-9][0-9]')):
 for p in sorted((d/'sources').rglob('*')):
  if not p.is_file() or p.stat().st_size<4096:continue
  data=p.read_bytes();h=hashlib.sha256(data).hexdigest();q=store/h
  if not q.exists():q.write_bytes(data)
  assert q.read_bytes()==data
  if not p.is_symlink():p.unlink();p.symlink_to(os.path.relpath(q,p.parent))
  rows.append(dict(path=str(p.relative_to(E)),stored=str(q.relative_to(E)),sha256=h,bytes=len(data)))
(E/'NGW_INPUT_INDEX.json').write_text(json.dumps(dict(inputs=rows,unique_inputs=len({r['sha256']for r in rows}),logical_bytes=sum(r['bytes']for r in rows),stored_bytes=sum((store/h).stat().st_size for h in {r['sha256']for r in rows})),indent=1)+'\n')
print('packed',len(rows),'snapshots')
