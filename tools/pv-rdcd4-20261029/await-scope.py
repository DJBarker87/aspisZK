"""Wait locally in <=50s intervals, then submit exactly once through scope.py.
Admission and the same-command barrier remain authoritative in scope.py.
"""
from pathlib import Path
from datetime import datetime,timezone
import time,json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
while True:
 stamps=[]
 p=E/'last-launch.json'
 if p.exists():stamps.append(json.load(open(p))['epoch'])
 for p in list(E.glob('*/admission-history.jsonl'))+list(E.glob('*/barrier-history.jsonl')):
  for line in p.read_text().splitlines():
   a=json.loads(line).get('admission',{})
   if a.get('allowed') is False and a.get('utc'):stamps.append(datetime.fromisoformat(a['utc']).timestamp())
 remaining=180-time.time()+max(stamps) if stamps else 0
 if remaining<=0:break
 print(f'Local cooldown, {remaining:.1f}s remaining; no host submission.',flush=True)
 time.sleep(min(50,remaining+0.1))
sys.exit(subprocess.call([sys.executable,str(R/'tools/pv-rdcd4-20261029/scope.py'),*sys.argv[1:]]))
