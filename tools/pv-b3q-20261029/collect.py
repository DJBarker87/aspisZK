"""Collect only text evidence, never compiled objects or executable artifacts."""
from pathlib import Path
import json,shutil,re,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');O=H/'export';O.mkdir(exist_ok=True);rows=[]
for p in sorted(H.glob('lean-*')):
 if not p.is_dir():continue
 q=p/'receipt/receipt.json'
 if q.exists():
  r=json.loads(q.read_text());rows.append(dict(attempt=r['attempt'],module=r['module'],exit=r['exit_status'],source_sha256=r['source_sha256'],receipt='receipts/'+p.name+'/receipt/receipt.json'))
 dest=O/'receipts'/p.name
 if dest.exists():shutil.rmtree(dest)
 shutil.copytree(p,dest)
for p in sorted(H.glob('native-*')):
 if not p.is_dir():continue
 dest=O/'receipts'/p.name
 if dest.exists():shutil.rmtree(dest)
 shutil.copytree(p,dest)
for pattern in ['*.json','*.jsonl']:
 for p in H.glob(pattern):shutil.copy2(p,O/p.name)
(O/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(lean=len(rows),passed=sum(r['exit']==0 for r in rows),failed=sum(r['exit']!=0 for r in rows))))
