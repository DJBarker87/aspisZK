#!/usr/bin/env python3
"""Index each source-changing attempt without suppressing failed receipts."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parents[1]
rows=[]
for d in sorted((B/'attempts').iterdir(),key=lambda p:int(p.name.rsplit('-',1)[1])):
 s=json.loads((d/'source.json').read_text());r=dict(attempt=d.name,**s,patch_sha256=hashlib.sha256((d/'source.patch').read_bytes()).hexdigest(),phases=[])
 for phase in ['charon','aeneas']:
  p=d/('extract-'+d.name+'-'+phase)
  if not (p/'receipt.json').exists():continue
  receipt=json.loads((p/'receipt.json').read_text());err=(p/'stderr.log').read_text()
  r['phases'].append(dict(phase=phase,receipt=str((p/'receipt.json').relative_to(B)),exit=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],error_prefix=err[:900] if receipt['exit_status'] else None,print_axioms='N/A: extraction, not Lean compilation'))
 rows.append(r)
(B/'attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
print('indexed',len(rows),'source-changing extraction attempts')
