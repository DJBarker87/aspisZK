"""Wait for documented admission cooldown/window, then retry one unlaunched ID.
No compiler retry is possible: check.py rejects an already-launched ID.
"""
from pathlib import Path
import datetime,json,subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028'
a=int(sys.argv[1]);m=sys.argv[2]
for retry in range(10):
 rows=[json.loads(p.read_text()) for p in E.glob('*refusal*.json')]
 now=time.time()
 deadline=max([datetime.datetime.fromisoformat(r['utc']).timestamp()+180 for r in rows]+[r.get('quiet_window_until',0) for r in rows]+[now])
 while time.time()<deadline:
  remaining=deadline-time.time()
  print('Admission wait:',round(remaining,1),'seconds; unlaunched ID',a,flush=True)
  time.sleep(min(60,remaining+.1))
 result=subprocess.run([sys.executable,str(R/'tools/pv-runjoin31-20261028/check.py'),str(a),m])
 if result.returncode not in [77,78,79]:sys.exit(result.returncode)
print('ten unlaunched admission refusals; return to compile-free work',flush=True)
sys.exit(78)
