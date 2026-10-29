import subprocess,fcntl
from pathlib import Path
with open('/private/tmp/pv-b3p6-resume15-submit.lock','w')as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 D=Path('evidence/pv-b3p6-20261028');T=Path('tools/pv-b3p6-20261028');host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028/'
 mods=['PV_B3P_Resume15Combined','PV_B3P_Resume15Axioms','PV_B3P_Resume15Focused'];paths=[str(D/'lean'/(m+'.lean'))for m in mods]
 subprocess.run(['git','add',*paths],check=True)
 if subprocess.run(['git','diff','--cached','--quiet']).returncode:subprocess.run(['git','commit','-m','Freeze the op227 resume15 proof audit cohort'],check=True)
 subprocess.run(['python3',str(T/'authority_resume15.py'),*mods],check=True)
 subprocess.run(['scp',str(D/'resume15/project-resolution-resume15.json'),str(T/'audits_resume15_host.py'),host+':'+H],check=True)
 subprocess.run(['scp',*paths,host+':'+H+'lean/'],check=True)
 subprocess.run(['ssh',host,'cd '+H+' && python3 preflight_resume15_host.py && python3 audits_resume15_host.py'],check=True)
