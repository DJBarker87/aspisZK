from pathlib import Path
import subprocess,json,sys
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/wire'
items=json.loads((e/'operations.json').read_text())
for x in items:
 receipts=[json.loads(f.read_text()) for f in e.glob('*-receipt.json')]
 if any(y['module']==x['module'].replace('.','/') and y['validation_exit']==0 for y in receipts):continue
 a=max(json.loads((e/'attempt-tally.json').read_text())['ids'])+1
 q=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-wire.py'),str(a),x['module']],cwd=r)
 if q.returncode:raise SystemExit(q.returncode)
