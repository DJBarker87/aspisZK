"""Retry only unlaunched reservation refusals, with fresh exclusive IDs.
Never retries a charged/failed compile. Keeps the full 180-second cooldown.
"""
from pathlib import Path
import subprocess,sys,json,datetime,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028'
first,last=int(sys.argv[1]),int(sys.argv[2]);module=sys.argv[3]
assert 44600<=first<=last<=44696 and last-first<10
for attempt in range(first,last+1):
 while True:
  refusals=[json.loads(p.read_text()) for p in E.glob('*refusal*.json')]
  latest=max((datetime.datetime.fromisoformat(r['utc']) for r in refusals),default=datetime.datetime.min.replace(tzinfo=datetime.timezone.utc))
  remaining=180-(datetime.datetime.now(datetime.timezone.utc)-latest).total_seconds()
  if remaining<=0:break
  print(f'cooldown: {remaining:.2f}s; next unused ID {attempt}',flush=True)
  time.sleep(min(60,remaining+.1))
 result=subprocess.run([sys.executable,str(R/'tools/pv-runjoin31-20261028/check.py'),str(attempt),module])
 if result.returncode!=78:sys.exit(result.returncode)
print('ten reservation refusals; no further ID scheduled',flush=True)
sys.exit(78)
