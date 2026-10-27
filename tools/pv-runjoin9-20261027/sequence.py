#!/usr/bin/env python3
"""Sequential focused dependency checks; stop at first refusal or failure."""
import json,pathlib,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2]
plan=json.loads((root/sys.argv[1]).read_text())
start,count,attempt=map(int,sys.argv[2:5])
for row in plan[start:start+count]:
 m=row['module'];assert m not in ['R1Z.EventsR1P2','R1Z.SimCostOuterRetry6']
 r=subprocess.run([sys.executable,str(root/'tools/pv-runjoin9-20261027/check.py'),str(attempt),m.replace('.','/'),row['source']],capture_output=True,text=True)
 print('\n'.join(s for s in r.stdout.splitlines() if s.startswith(('LAUNCH','RECEIPT','RESERVATION'))),flush=True)
 if r.returncode:print(r.stderr,flush=True);sys.exit(r.returncode)
 attempt+=1
