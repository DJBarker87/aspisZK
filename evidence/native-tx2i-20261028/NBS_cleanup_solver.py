from pathlib import Path
import subprocess,shlex,json,sys
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json
p=Path('/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028/NBS_tmp')
removed=[]
if p.exists():
 for q in p.rglob('*'):
  if q.is_file():
   removed.append(dict(path=str(q),bytes=q.stat().st_size));q.unlink()
print(json.dumps(removed))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/('NBS_'+sys.argv[1]+'_SOLVER_CLEANUP.json')).write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');assert r.returncode==0
