"""Disjoint statement/axiom audit portions, followed by the combined audit."""
from pathlib import Path
import json,subprocess,sys
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume3'
x=json.loads((e/'combined-audit-manifest.json').read_text())
for m in x['part_modules']+['R1Z.PV_Join_CombinedAudit']:
 a=max(json.loads((e/'attempt-tally.json').read_text())['ids'])+1
 p=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-check3.py'),str(a),m],cwd=r)
 if p.returncode:raise SystemExit(p.returncode)
