"""Freeze job-owned proof inputs and invoke the existing private compiler serially."""
import subprocess,sys,fcntl
_lock=open("/private/tmp/pv-b3p6-resume15-submit.lock","w")
fcntl.flock(_lock,fcntl.LOCK_EX)
from pathlib import Path
T=Path('tools/pv-b3p6-20261028');D=Path('evidence/pv-b3p6-20261028');host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028/'
mods=sys.argv[1:];paths=[str(D/'lean'/(m+'.lean')) for m in mods]
subprocess.run(['git','add',*paths],check=True)
if subprocess.run(['git','diff','--cached','--quiet']).returncode:subprocess.run(['git','commit','-m','Bind changed op227 source functions by named stages'],check=True)
subprocess.run(['python3',str(T/'authority_resume15.py'),*mods],check=True)
subprocess.run(['scp',str(D/'resume15/project-resolution-resume15.json'),host+':'+H],check=True)
subprocess.run(['scp',*paths,host+':'+H+'lean/'],check=True)
result=subprocess.run(['ssh',host,'cd '+H+' && python3 continue_resume15_host.py modules '+' '.join(mods)])
if result.returncode:
 # Read the proof diagnostic only after that invocation has ended, while still
 # holding the same serialization lock; no parallel ssh session is opened.
 diagnostic="import json;from pathlib import Path;t=json.loads(Path('TALLY-resume15.json').read_text());r=t.get('receipts',[]);print(Path(r[-1]['receipt']).with_name('stdout.log').read_text() if r else 'No charged Lean receipt')"
 import shlex
 subprocess.run(['ssh',host,'cd '+H+' && python3 -c '+shlex.quote(diagnostic)],check=False)
 raise SystemExit(result.returncode)

