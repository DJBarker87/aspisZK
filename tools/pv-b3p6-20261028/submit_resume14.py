"""Freeze job-owned proof inputs and invoke the existing private compiler serially."""
import subprocess,sys,fcntl
_lock=open("/private/tmp/pv-b3p6-resume14-submit.lock","w")
fcntl.flock(_lock,fcntl.LOCK_EX)
from pathlib import Path
T=Path('tools/pv-b3p6-20261028');D=Path('evidence/pv-b3p6-20261028');host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028/'
mods=sys.argv[1:];paths=[str(D/'lean'/(m+'.lean')) for m in mods]
subprocess.run(['git','add',*paths],check=True)
if subprocess.run(['git','diff','--cached','--quiet']).returncode:subprocess.run(['git','commit','-m','Correct op227 links with explicit caller obligations'],check=True)
subprocess.run(['python3',str(T/'authority_resume14.py'),*mods],check=True)
subprocess.run(['scp',str(D/'resume14/project-resolution-resume14.json'),host+':'+H],check=True)
subprocess.run(['scp',*paths,host+':'+H+'lean/'],check=True)
subprocess.run(['ssh',host,'cd '+H+' && python3 continue_resume14_host.py modules '+' '.join(mods)],check=True)
