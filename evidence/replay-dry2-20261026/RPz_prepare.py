"""Prepare job inputs and isolated trusted-library links; no build infrastructure."""
from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026')
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
g=json.loads((B/'RPz_source-plan.json').read_text()); h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots={'AeneasMeta','Aeneas','Mathlib','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}
lib=B/'RPz_trusted';lib.mkdir(exist_ok=True); artifacts={}
for root in sorted(roots):
 for p in sorted(C.glob(root+'*')):
  if p.name!=root and not p.name.startswith(root+'.'):continue
  q=lib/p.name
  if not q.exists():q.symlink_to(p,target_is_directory=p.is_dir())
  for f in ([p] if p.is_file() else sorted(p.rglob('*'))):
   if f.is_file():artifacts[str(f)]={'sha256':h(f),'bytes':f.stat().st_size}
for p in sorted((T/'lib/lean').rglob('*')):
 if p.is_file() and ('.olean' in p.name or p.suffix=='.ir' or p==T/'bin/lean'):artifacts[str(p)]={'sha256':h(p),'bytes':p.stat().st_size}
for p in [T/'bin/lean',T/'bin/lake',B/'S2W_run_host.py',Path('/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py')]:artifacts[str(p)]={'sha256':h(p),'bytes':p.stat().st_size}
trusted=dict(toolchain=subprocess.check_output([str(T/'bin/lean'),'--version'],text=True).strip(),artifacts=artifacts,scope='Pinned toolchain and pinned third-party library cache only; no repository objects',lake_manifest=json.loads((B/'RPz_lake-pins.json').read_text()))
(B/'RPz_trusted-base.json').write_text(json.dumps(trusted,indent=2)+'\n')
rows=[]
for m in g['order']:
 x=g['modules'][m]; rel='RPz_sources/'+m.replace('.','/')+'.lean'; dst=B/rel
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(B/'research'/x['source'],dst);assert h(dst)==x['sha256']
 (B/'RPz_objects'/Path(m.replace('.','/'))).parent.mkdir(parents=True,exist_ok=True)
 rows.append(dict(module=m,source=rel,repository_source=x['source'],source_sha256=h(dst),imports=x['imports'],object='RPz_objects/'+m.replace('.','/')+'.olean'))
(B/'RPz_inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
print('repository inputs',len(rows),'trusted artifacts',len(artifacts))
