"""Ordered missing audit targets, one capped compile at a time; stop on errors."""
from pathlib import Path
import json,subprocess,sys
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume3'
mods=json.loads((r/'evidence/pv-join-20261026/resume/final-audit-preflight.json').read_text())['missing']
start=int(sys.argv[1]);end=int(sys.argv[2])
for m in mods[start:end]:
 used=json.loads((e/'attempt-tally.json').read_text());a=max(used['ids'])+1
 p=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-check3.py'),str(a),m],cwd=r)
 if p.returncode:raise SystemExit(p.returncode)
