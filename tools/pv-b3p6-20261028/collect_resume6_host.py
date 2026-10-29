"""Archive exact source snapshots, refusals and receipts for IDs60800–60899."""
from pathlib import Path
import json,shutil,hashlib
from run import H
O=H/'archive-resume6';R=O/'receipts';R.mkdir(parents=True,exist_ok=True);index=[];snapshot_errors=[]
for p in sorted(H.glob('lean-608[0-9][0-9]*')):
 if not p.is_dir():continue
 dest=R/p.name;dest.mkdir(exist_ok=True)
 for f in p.rglob('*'):
  if not f.is_file() or f.suffix in ['.olean','.ilean']:continue
  q=dest/f.relative_to(p);q.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(f,q)
 if not (p/'receipt/receipt.json').exists():continue
 x=json.loads((p/'receipt/receipt.json').read_text())
 actual=hashlib.sha256((p/'source.lean').read_bytes()).hexdigest()
 if actual!=x['source_sha256']:snapshot_errors.append(dict(label=p.name,expected=x['source_sha256'],snapshot=actual))
 index.append(dict(label=p.name,module=x['module'],attempt=x['attempt'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],lean_source_revision=x['lean_source_revision'],source_sha256=x['source_sha256'],source_snapshot_sha256=actual,print_axioms=x['print_axioms'],receipt='receipts/'+p.name+'/receipt/receipt.json'))
for name in ['TALLY-resume6.json','project-resolution-resume6.json','external-verification-resume6.json']:
 shutil.copy2(H/name,O/name)
(O/'receipt-index.json').write_text(json.dumps(index,indent=2)+'\n')
(O/'source-snapshot-check.json').write_text(json.dumps(dict(checked=len(index),mismatches=snapshot_errors),indent=2)+'\n')
print(json.dumps(dict(receipts=len(index),snapshot_errors=snapshot_errors)))
