"""Retry admission holds only, after three minutes, with fresh receipt labels."""
from pathlib import Path
import subprocess,sys,time,json,datetime
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
label=sys.argv[1];first=int(sys.argv[2]);cmd=sys.argv[3:]
previous=H/'candidate'/f'{label}-{first-1:03}'/'reservation.json'
if previous.exists():
 prior=json.loads(previous.read_text());stamp=prior.get('utc',previous.stat().st_mtime)
 if isinstance(stamp,str):stamp=datetime.datetime.fromisoformat(stamp).timestamp()
 until=stamp+180
 while time.time()<until:
  remaining=until-time.time();print('initial reservation cooldown',round(remaining),'seconds',flush=True);time.sleep(min(60,remaining))
for attempt in range(first,11):
 if attempt!=first:
  for _ in range(3):print('reservation cooldown: 60 seconds',flush=True);time.sleep(60)
 name=f'{label}-{attempt:03}';r=subprocess.run(['python3',str(H/'native.py'),'candidate',name,*cmd]);print(name,'exit',r.returncode,flush=True)
 if r.returncode!=78:sys.exit(r.returncode)
print('Ten admission holds exhausted; no command executed for the held launches',flush=True);sys.exit(78)
