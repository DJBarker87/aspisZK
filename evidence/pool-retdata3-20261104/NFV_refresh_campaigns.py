"""Regenerate reporting flags exclusively from immutable terminal stdout."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
for f in ['NFV_ACCOUNT_CAMPAIGN.jsonl','NFV_NATIVE_CAMPAIGN.jsonl']:
 p=E/f;rows=[json.loads(l) for l in p.read_text().splitlines()]
 for row in rows:
  a=row['attempt'];out=(E/a/'stdout.log').read_text();rc=json.loads((E/a/'receipt.json').read_text())
  row['exit']=rc['exit_status'];row['timeout']='timed out' in out.lower();row['unwind']='unwinding assertion' in out
  start=out.rfind('Failed Checks:');row['failed_check']=out[start:out.index('\n\n',start)] if start>=0 and '\n\n' in out[start:] else ''
 p.write_text(''.join(json.dumps(row)+'\n' for row in rows))
# Every attempt remains authoritative, including those stopped between campaign rows.
print('Reporting refreshed; raw receipts and source snapshots unchanged')
