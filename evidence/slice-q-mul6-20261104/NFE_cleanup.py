"""Remove only this job's rebuildable workspace outputs; retain its entire cache."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-q-mul6-20261029';C=P/'codex-cx-slice-q-mul6-cache-20261029'
exports=json.loads(INPUT)
for x in exports:
 p=Path(x['destination']);assert p.is_relative_to(C) and hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256']
removed=[]
for n in ['NFE_objects','NFE_tmp','NFE_native']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
assert C.is_dir()
print(json.dumps(dict(removed=removed,cache_retained=str(C),source_workspace_retained=str(B/'NFE_generated'),exports_verified=len(exports),formal_attempts_terminal=100)))
'''.replace('INPUT',repr((E/'NFE_EXPORTS.json').read_text()))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NFE_CLEANUP.json').write_text(r.stdout);print(r.stdout)
