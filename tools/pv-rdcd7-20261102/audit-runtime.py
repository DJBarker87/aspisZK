"""Run fixed NEP_Driver as a standalone runtime with its own private data env."""
from pathlib import Path
import os,json,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd7-20261102')
e=json.load(open(D/'env-J.json'));env=os.environ.copy()
for k,v in e.items():
 if isinstance(v,str):env[k]=v
out=D/'raw-audit';out.mkdir(exist_ok=True)
cmd=[e['LEAN'],'-M7000','--run',str(D/'lean-sources/R1Z/PV_RDCD5_NEPDriver.lean')]
print('NEP standalone command',json.dumps(cmd),flush=True)
r=subprocess.run(cmd,cwd=out,env=env)
raise SystemExit(r.returncode)
