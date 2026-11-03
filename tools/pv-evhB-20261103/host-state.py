"""Read-only final own-scope and quiet-window snapshot."""
from pathlib import Path
import subprocess,json,shlex
E=Path('evidence/pv-evhB-20261103')
code=r'''
import pathlib,subprocess,json,time,datetime
marker=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
units=subprocess.run(['systemctl','--user','list-units','--state=running,activating','--plain','--no-pager','--no-legend','pv-evhB-*'],text=True,capture_output=True)
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),epoch=time.time(),units_exit=units.returncode,own_active_units=units.stdout,stderr=units.stderr,quiet_window=json.loads(marker.read_text()) if marker.exists() else None)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'host-final.json').write_text(json.dumps(x,indent=2)+'\n')
assert x['units_exit']==0 and not x['own_active_units'].strip(),x
print('PASS no own active scopes; quiet-window snapshot recorded')
