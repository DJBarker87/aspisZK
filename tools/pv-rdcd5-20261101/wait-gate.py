"""Local, compile-free gate waiting. Never submits work or edits the gate.
Each sleep is at most 60 seconds; poll-gate enforces ten-minute spacing.
"""
from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,sys,time
R=Path(__file__).resolve().parents[2]
p=R/'evidence/pv-rdcd5-20261101/GATE-POLLS.jsonl'
while True:
    rows=[json.loads(x) for x in p.read_text().splitlines()] if p.exists() else []
    if rows and rows[-1]['flag_exists']:
        print('Host-restored flag found; read the recorded contents before proceeding.',flush=True)
        break
    if len(rows)>=24:
        print('24 absent-flag polls exhausted: gated, budget unspent. No host scope submitted.',flush=True)
        break
    delay=max(0,600-(datetime.now(timezone.utc)-datetime.fromisoformat(rows[-1]['utc'])).total_seconds()) if rows else 0
    if delay:
        time.sleep(min(delay,60))
        continue
    q=subprocess.run([sys.executable,str(R/'tools/pv-rdcd5-20261101/poll-gate.py')],cwd=R)
    assert q.returncode==0,q.returncode
