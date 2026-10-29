"""Ruling (m'): admission-only retries with SAME unlaunched ID.
Stop on first compiler verdict. Never advance absent an already-used rejection."""
import subprocess,time,json,sys
from pathlib import Path
E=Path('evidence/pv-evh4-20261029');attempt=int(sys.argv[1]);module=sys.argv[2]
for retry in range(9):
 for q in E.glob('refusal-*.json'):
  remaining=180-(time.time()-json.loads(q.read_text())['epoch'])
  while remaining>0:
   time.sleep(min(30,remaining));remaining=180-(time.time()-json.loads(q.read_text())['epoch'])
 print('SAME-ID ADMISSION',attempt,'retry',retry+1,flush=True)
 result=subprocess.run([sys.executable,'tools/pv-evh4-20261029/compile.py',str(attempt),module])
 if result.returncode!=78:sys.exit(result.returncode)
print('Admission retry limit reached; no compiler launched',flush=True)
sys.exit(78)
