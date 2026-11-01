"""Read-only rebuild gate poll; never creates or modifies the external flag."""
from pathlib import Path
from datetime import datetime, timezone
import json
R=Path(__file__).resolve().parents[2]
p=R/'evidence/pv-rdcd5-20261101/GATE-POLLS.jsonl'
flag=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
old=[json.loads(line) for line in p.read_text().splitlines()] if p.exists() else []
now=datetime.now(timezone.utc)
if old:
    delta=(now-datetime.fromisoformat(old[-1]['utc'])).total_seconds()
    if delta<600:
        print(f'Next poll in {600-delta:.1f}s; no launch authorized')
        raise SystemExit(78)
assert len(old)<24, 'Required 24 polls already recorded; report gated budget unspent'
row=dict(poll=len(old)+1,utc=now.isoformat(),flag_exists=flag.exists(),host_scopes_launched=0)
if flag.exists():row['contents']=flag.read_text()
with p.open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps(row))
