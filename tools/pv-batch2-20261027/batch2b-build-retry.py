from pathlib import Path
import datetime,json,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
mode=sys.argv[1]
for n in range(1,11):
 label=f'batch2b-build-{mode}-{n:03}'
 out=H/'candidate'/label
 if out.exists():
  r=json.loads((out/'reservation.json').read_text())
  assert r['allowed'] is False, 'existing admitted job must never be rerun'
 else:
  status=subprocess.run(['python3',str(H/'build.py'),'candidate',mode,label]).returncode
  print(label,status,flush=True)
  if status!=78:sys.exit(status)
  r=json.loads((out/'reservation.json').read_text())
 stamp=r.get('utc',out.stat().st_mtime)
 if isinstance(stamp,str):stamp=datetime.datetime.fromisoformat(stamp).timestamp()
 while time.time()<stamp+180:time.sleep(min(60,stamp+180-time.time()))
raise SystemExit(78)
