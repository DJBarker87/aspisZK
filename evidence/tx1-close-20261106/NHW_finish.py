"""Own post-restore cleanup only; never remove retained caches or keys."""
from pathlib import Path
import subprocess,json
B=Path('/home/dombarker/project-offloads/codex-cx-tx1-close-20261106');assert B.name=='codex-cx-tx1-close-20261106'
import shutil
processes=subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines()
owned=[p for p in processes if 'S2W_run_host.py NHW_' in p]
assert not owned,owned
removed=[]
for n in ['NHW_objects','NHW_native','NHW_tmp']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(active_owned_scopes=owned,removed_own_rebuildable_outputs=removed,cache_retained='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHW_exports_20261106',disk=subprocess.check_output(['df','-h',str(B)],text=True))))
