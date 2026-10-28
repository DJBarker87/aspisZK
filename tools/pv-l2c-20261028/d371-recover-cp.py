"""Task-local retry of one prelaunch SSH255; never submits a build."""
from pathlib import Path
import subprocess,json,datetime,time,sys
R=Path(__file__).resolve().parents[2]
E=R/'evidence/pv-l2c-20261028/resume-d371'
first=json.loads((E/'account-probe3-cp-recovery.json').read_text())
assert first['exit']==255 and first['compiler_launched'] is False
command=first['command']
last=first
for attempt in range(2,11):
    elapsed=(datetime.datetime.now(datetime.timezone.utc)-datetime.datetime.fromisoformat(last['utc'])).total_seconds()
    cooldown=max(0,60-elapsed)
    print('Transport retry',attempt,'after cooldown',cooldown,'seconds; no build submission',flush=True)
    if cooldown:time.sleep(cooldown)
    start=time.monotonic()
    p=subprocess.run(command,text=True,capture_output=True)
    last={'attempt':attempt,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'command':command,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,
      'wall_seconds':time.monotonic()-start,'compiler_launched':False}
    (E/('account-probe3-cp-retry-'+str(attempt)+'.json')).write_text(json.dumps(last,indent=2)+'\n')
    print(json.dumps(last),flush=True)
    if p.returncode==0:sys.exit(0)
    if p.returncode!=255:sys.exit(p.returncode)
sys.exit(255)
