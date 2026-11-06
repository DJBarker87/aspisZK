"""Run only between scopes: keep canonical full receipts; index them by SHA."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;P=E/'NLM_ATTEMPTS.jsonl'
rows=[]
for line in P.read_text().splitlines():
 r=json.loads(line);p=E/r['attempt']/'receipt.json';raw=p.read_bytes();full=json.loads(raw)
 for k,v in full.items():
  if k=='deps_fingerprint' and k not in r:continue
  assert r[k]==v,(r['attempt'],k)
 summary={k:v for k,v in full.items() if k!='deps_fingerprint'}
 summary.update(full_receipt=str(p.relative_to(E)),full_receipt_sha256=hashlib.sha256(raw).hexdigest())
 rows.append(summary)
P.write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps(dict(receipts=len(rows),index_bytes=P.stat().st_size,canonical_receipts_unchanged=True)))
