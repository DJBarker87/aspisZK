"""Admission-only retries with next unused IDs and full 180 second cooldown.
Stop on the first actual compilation, regardless of its verdict."""
import subprocess,time,json,sys
from pathlib import Path
E=Path('evidence/pv-evh4-20261029');start=int(sys.argv[1]);module=sys.argv[2]
for a in range(start,min(start+8,73697)):
 for q in E.glob('refusal-*.json'):
  remaining=180-(time.time()-json.loads(q.read_text())['epoch'])
  while remaining>0:
   time.sleep(min(30,remaining));remaining=180-(time.time()-json.loads(q.read_text())['epoch'])
 print('NEXT ADMISSION',a,flush=True)
 result=subprocess.run([sys.executable,'tools/pv-evh4-20261029/compile.py',str(a),module])
 if result.returncode!=78:sys.exit(result.returncode)
print('Ten total admission refusals; no compiler launched',flush=True)
sys.exit(78)
