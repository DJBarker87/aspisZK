#!/usr/bin/env python3
"""Serial declared native attempts; intended failures must reach verification."""
from pathlib import Path
import json,subprocess,sys,re
E=Path(__file__).resolve().parent
jobs=json.loads((E/sys.argv[1]).read_text())
for job in jobs:
 cmd=['python3',str(E/'NEB_kani.py'),job['attempt'],job['target']]+([job['flag']] if job.get('flag') else [])
 r=subprocess.run(cmd)
 p=E/job['attempt']/'receipt.json'
 if not p.exists():raise SystemExit('attempt has no terminal receipt; no later launch')
 rc=json.loads(p.read_text());text=(p.parent/'stdout.log').read_text()
 if rc['exit_status']!=job['expected_exit'] or 'VERIFICATION:- '+('SUCCESSFUL' if job['expected_exit']==0 else 'FAILED') not in text:raise SystemExit('unexpected native result; stop queue')
 if job['expected_exit']:
  assert re.findall(r'\*\* (\d+) of \d+ failed',text)[-1]=='1','negative has additional failures'
  assert job['failure'] in text.split('Failed Checks:',1)[1],'wrong negative failure'
