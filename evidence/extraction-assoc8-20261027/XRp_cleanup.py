from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
remote=r'''
from pathlib import Path
import hashlib,json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc8-20261027')
p=B/'XRp_objects'
assert p.parent==B and not p.is_symlink()
files=[]
if p.exists():
 for f in sorted(p.rglob('*')):
  if f.is_file():files.append({'path':str(f.relative_to(B)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size})
 shutil.rmtree(p)
print(json.dumps({'removed_directory':str(p),'files':files,'bytes_removed':sum(f['bytes'] for f in files),'keys_touched':False,'shared_paths_touched':False,'solver_temp_files':'none: no Kani runs','sources_and_receipts_retained':True}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True,capture_output=True,check=True)
x=json.loads(r.stdout);(E/'XRp_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n')
print({'files_removed':len(x['files']),'bytes_removed':x['bytes_removed']})
