from pathlib import Path
import shutil,hashlib,json
B=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108'); rows=[]
seeds=[('NKN','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKN_20261108/NKN_exports_20261108'),('NKA','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKA_exports_final_20261108')]
for tag,root in seeds:
 root=Path(root)
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  q=B/'NKQ_seed'/tag/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  before=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==before
  rows.append(dict(source=str(p),destination=str(q),sha256=before,bytes=q.stat().st_size))
(B/'NKQ_SEED_PINS.json').write_text(json.dumps(dict(files=rows,bytes=sum(x['bytes'] for x in rows)),indent=2))
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows))))
