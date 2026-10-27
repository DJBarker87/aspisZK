from pathlib import Path
import subprocess,sys,json,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
# Sequential only. A refusal ends this queue so the owner can observe the
# cooldown; it never falls through to another capped scope.
for kind,op,suffix in [('forest',133,'01'),('forest',132,'01'),('forest',228,'01'),('copies',117,'01'),('copies',121,'01'),('copies',222,'01'),('copies',224,'01'),('copies',226,'01'),('copies',227,'01')]:
 command=['python3',str(H/('extract_forest.py' if kind=='forest' else 'extract_copies.py')),str(op),suffix]
 print('START',kind,op,suffix,flush=True);r=subprocess.run(command);print('END',kind,op,r.returncode,flush=True)
 if r.returncode==78:sys.exit(78)
 if r.returncode not in [0,1,2,124]:sys.exit(r.returncode)
