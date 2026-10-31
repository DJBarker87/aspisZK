from NEF_host import *
import hashlib
admit('NEF_SETUP001')
r=py('''from pathlib import Path
import shutil,json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-slice-q-fnptr-20261029')
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
shutil.copy2(w/'S2W_run_host.py',b/'S2W_run_host.py')
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-fnptr-cache-20261029');c.mkdir(exist_ok=True)
imports=[]
for name in ['codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-front3-cache-20261028','codex-cx-slice-q-leaves-cache-20261029']:
 root=Path('/home/dombarker/project-offloads')/name
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(root);q=c/rel;h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():
   if hashlib.sha256(q.read_bytes()).hexdigest()!=h:
    imports.append(dict(source=str(p),sha256=h,status='collision retained first'));continue
  else:q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  imports.append(dict(source=str(p),destination=str(q),sha256=h,status='copied'))
(b/'NEF_CACHE_IMPORTS.json').write_text(json.dumps(imports,indent=2))
s=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026/src')
print(json.dumps(dict(source_exists=s.exists(),runner_sha256=hashlib.sha256((b/'S2W_run_host.py').read_bytes()).hexdigest(),cache_imports=len(imports))))
''');assert r.returncode==0,r.stderr;print(r.stdout)
r=py("from pathlib import Path;print((Path("+repr(B)+")/'NEF_CACHE_IMPORTS.json').read_text())");assert r.returncode==0
(E/'NEF_CACHE_IMPORTS.json').write_text(r.stdout)
