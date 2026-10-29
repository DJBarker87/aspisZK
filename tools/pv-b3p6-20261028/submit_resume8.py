"""Commit exact new proof sources, resolve h5 authority, upload privately, compile serially."""
import subprocess,sys
from pathlib import Path
mods=sys.argv[1:];D=Path('evidence/pv-b3p6-20261028');T=Path('tools/pv-b3p6-20261028');H='dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-b3p6-20261028/'
paths=[str(D/'lean'/(m+'.lean'))for m in mods]
subprocess.run(['git','add',*paths,str(T/'digest227_resume8.py'),str(T/'submit_resume8.py'),str(T/'continue_resume8_host.py')],check=True)
if subprocess.run(['git','diff','--cached','--quiet']).returncode:subprocess.run(['git','commit','-m','Refine named op227 stages before focused compilation'],check=True)
subprocess.run(['python3',str(T/'authority_resume8.py'),*mods],check=True)
subprocess.run(['scp',str(D/'resume8/project-resolution-resume8.json'),str(T/'continue_resume8_host.py'),H],check=True)
subprocess.run(['scp',*paths,H+'lean/'],check=True)
subprocess.run(['ssh','dombarker@100.108.41.90','cd /home/dombarker/project-offloads/codex-pv-b3p6-20261028 && python3 continue_resume8_host.py modules '+' '.join(mods)],check=True)
