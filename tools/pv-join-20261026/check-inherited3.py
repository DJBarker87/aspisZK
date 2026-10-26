"""Focused checks of inherited drafts and new fixture-boundary consumers."""
from pathlib import Path
import subprocess,json,sys
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume3'
mods=['ClosureCheckpoint','Inspect','NativeNeg101','PublicOp20','AuditProjection','LedgerSource','PublicDataIff','FixtureInputs','FixtureSelected','FixtureData']
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for m in mods[start:]:
 a=max(json.loads((e/'attempt-tally.json').read_text())['ids'])+1
 p=subprocess.run([sys.executable,str(r/'tools/pv-join-20261026/host-check3.py'),str(a),'R1Z/PV_Join_'+m],cwd=r)
 if p.returncode:print('Stopped at index',mods.index(m),flush=True);raise SystemExit(p.returncode)
