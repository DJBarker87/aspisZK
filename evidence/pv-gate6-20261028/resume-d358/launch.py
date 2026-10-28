"""Single launch intent; recover this record after transport failure, never relaunch."""
from pathlib import Path
import os,json,time,subprocess,hashlib
D=Path(__file__).resolve().parent
fd=os.open(D/'launch-intent.json',os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
with os.fdopen(fd,'w') as f:json.dump(dict(utc=time.time(),purpose='D358 one authorized Stage B window'),f)
with (D/'driver.log').open('wb') as log:
 p=subprocess.Popen(['bash',str(D/'quiet-window.sh')],cwd=D,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
x=dict(pid=p.pid,utc=time.time(),script_sha256=hashlib.sha256((D/'quiet-window.sh').read_bytes()).hexdigest(),expected_time='optimized proof generation and P_R1 elimination, no compilation')
(D/'launch.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
