"""Create our own immutable, expiring timing marker; never edit/delete one."""
from pathlib import Path
import json,os,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');M=H.parent/'QUIET_WINDOW.json'
subprocess.run(['python3',str(H/'quiet-preflight.py'),str(H/'quiet-before-window.json')],check=True,stdout=subprocess.DEVNULL)
start=time.time();r=dict(owner='pv-c474-20261029',start=start,until=start+900,purpose='D491 experimental paired actual-client timing; no compilation')
fd=os.open(M,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o644)
with os.fdopen(fd,'w') as f:json.dump(r,f);f.write('\n')
(H/'window-start.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
