from pathlib import Path
import subprocess,json,sys
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/wire';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
files=[p/'PV_Join_Wire_ConstantEntries.lean']+sorted(p.glob('PV_Join_Wire_Entry*.lean'))
for f in files:
 m='R1Z/'+f.stem
 receipts=[json.loads(f.read_text()) for f in e.glob('*-receipt.json')]
 if any(y['module']==m and y['validation_exit']==0 for y in receipts):continue
 a=max(json.loads((e/'attempt-tally.json').read_text())['ids'])+1
 q=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-wire.py'),str(a),m],cwd=r)
 if q.returncode:raise SystemExit(q.returncode)
