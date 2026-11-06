from pathlib import Path
import shutil,hashlib,json
B=Path('/home/dombarker/project-offloads/codex-cx-tx1-top-20261110');rows=[]
seeds=[('NLJ','/home/dombarker/project-offloads/codex-cx-tx1-prepare-20261110/NLJ_exports_20261110'),('NLC','/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109/NLC_exports_20261109'),('NLS','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLS_20261110/NLS_exports_20261110')]
for tag,root in seeds:
 root=Path(root);assert root.is_dir(),str(root)
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  q=B/'NLV_seed'/tag/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  before=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==before
  rows.append(dict(source=str(p),destination=str(q),sha256=before,bytes=q.stat().st_size))
(B/'NLV_SEED_PINS.json').write_text(json.dumps(dict(files=rows,bytes=sum(x['bytes'] for x in rows)),indent=2))
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows))))
