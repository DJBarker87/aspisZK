#!/usr/bin/env python3
"""Serial attempts only; stop on controller/infrastructure faults, retain tool failures."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for i in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a='NMH_E%03d'%i
 assert not (E/a/'receipt.json').exists(), 'immutable attempt already exists'
 p=subprocess.run([sys.executable,str(E/'NMH_run.py'),a])
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP missing receipt for '+a)
 rc=json.loads((E/a/'receipt.json').read_text())
 print(json.dumps(dict(attempt=a,controller_exit=p.returncode,tool_exit=rc['exit_status'])),flush=True)
 if p.returncode!=rc['exit_status'] and not (p.returncode==1 and rc['exit_status']<0):raise SystemExit('STOP controller failure')
