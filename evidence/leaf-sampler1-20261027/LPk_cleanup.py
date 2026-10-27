"""Remove only rebuildable outputs owned by this job, after hashing them."""
from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
code='''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027')
assert b.name=='codex-cx-leaf-sampler1-20261027'
for p in b.glob('LPk_[KL]*/receipt.json'):
 r=json.loads(p.read_text());cg=Path(r['cgroup'])
 assert not cg.exists() or not (cg/'cgroup.procs').read_text().strip(),str(cg)
rows=[]
for name in ['LPk_target','LPk_objects','LPk_tmp']:
 root=b/name
 if not root.exists():continue
 assert root.parent==b and not root.is_symlink()
 for p in root.rglob('*'):
  if p.is_file():
   data=p.read_bytes();rows.append(dict(path=str(p.relative_to(b)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
 shutil.rmtree(root)
(b/'LPk_CLEANUP.json').write_text(json.dumps({'owned_scopes_terminal':True,'only_owned_build_cache_and_tmp_removed':True,'removed_files':len(rows),'removed_bytes':sum(r['bytes'] for r in rows),'files':rows},indent=2)+'\\n')
'''
r=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True)
(E/'LPk_cleanup.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
subprocess.run(['scp','-q',H+':/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027/LPk_CLEANUP.json',str(E/'LPk_CLEANUP.json')],check=True)
