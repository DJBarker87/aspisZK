"""Run a matched control with precisely the retained positive's native inputs."""
from pathlib import Path
import json,subprocess,sys,os
E=Path(__file__).resolve().parent
positive,control,harness=sys.argv[1:]
p=E/'NKO_NATIVE_INPUTS.json';saved=p.read_bytes()
x=json.loads(saved)
for n in x:
 q=E/positive/'sources'/'NKO_src'/n
 assert q.is_file(),q
 x[n]=q.read_text()
p.write_text(json.dumps(x,indent=2)+'\n')
try:
 env=os.environ.copy();env['NKO_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NKO_run.py'),control,'kani',harness],env=env)
finally:p.write_bytes(saved)
sys.exit(r.returncode)
