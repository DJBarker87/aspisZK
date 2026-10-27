"""Sequential focused queue, respecting the own-job admission cooldown.
No retries of failed compiles. Reservation refusals retire IDs in the runner.
"""
from pathlib import Path
import subprocess,sys,time,json,datetime
root=Path(__file__).resolve().parents[2]
runner=root/'tools/pv-cb3-20261026/resume6_lean.py'
state=root/'evidence/pv-cb3-20261026/RESUME6_ADMISSION_STATE.json'
for module in sys.argv[1:]:
    for retry in range(10):
        if state.exists():
            d=json.loads(state.read_text())
            if not d.get('allowed',False):
                left=datetime.datetime.fromisoformat(d['utc']).timestamp()+181-time.time()
                if left>0:
                    print(f'cooldown {left:.1f}s before {module}, reservation retry {retry+1}/10',flush=True)
                    # This runner is polled asynchronously; never blocks the agent turn.
                    time.sleep(left)
        code=subprocess.run([sys.executable,'-u',str(runner),module],cwd=root).returncode
        if code==0:break
        if code!=78:sys.exit(code)
        print(f'refused {module}; no compiler charged',flush=True)
    else:sys.exit(78)
