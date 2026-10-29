"""Collect receipts under the same local serialization lock as submissions."""
import fcntl,subprocess
from pathlib import Path
with open('/private/tmp/pv-b3p6-resume15-submit.lock','w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028'
 subprocess.run(['ssh',host,'cd '+H+' && python3 collect_resume15_host.py'],check=True)
 subprocess.run(['scp','-r',host+':'+H+'/archive-resume15/.','evidence/pv-b3p6-20261028/resume15/'],check=True)
