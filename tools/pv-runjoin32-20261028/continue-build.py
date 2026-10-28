"""Run planned dependency chunks sequentially; stop for inspection on any failure."""
from pathlib import Path
import sys,json,subprocess,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028';plan=json.loads((E/'build-plan.json').read_text())
for idx in range(int(sys.argv[1]),len(plan['chunks'])):
 a=51302+idx
 for retry in range(10):
  r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin32-20261028/chunk.py'),str(a),str(idx)])
  if r.returncode not in [77,78]:break
  print('ADMISSION COOLDOWN',a,'retry',retry+1,flush=True)
  for _ in range(3):time.sleep(60);print('COOLDOWN TICK',a,flush=True)
 if r.returncode:sys.exit(r.returncode)
 print('PROGRESS',idx+1,'/',len(plan['chunks']),'planned chunks',flush=True)
