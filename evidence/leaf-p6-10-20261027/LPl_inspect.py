from pathlib import Path
import subprocess,json
E=Path('evidence/leaf-p6-10-20261027');E.mkdir(exist_ok=True)
# Inspect only the adopted coherent workspace; no alternate object path.
code="""from pathlib import Path
import json
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
print(json.dumps({'objects':[str(p.relative_to(root)).removesuffix('.olean').replace('/','.') for root in [B,B/'objects'] for p in root.rglob('*.olean') if len(p.relative_to(root).parts)<4], 'sources':{str(p.relative_to(B)).removesuffix('.lean').replace('/','.'):p.read_text() for p in B.rglob('*.lean') if len(p.relative_to(B).parts)<4}}))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90',"python3 - <<'PYREMOTE'\n"+code+'\nPYREMOTE'],text=True,capture_output=True,check=True)
h=json.loads(r.stdout);(E/'LPl_host-inventory.json').write_text(json.dumps({'objects':h['objects']},indent=2)+'\n')
files={p.stem:p for p in Path('lean').rglob('*.lean')}
for folder in ['leaf-p6-1-20261027','leaf-p6-3-20261027','leaf-p6-7-20261027','leaf-p6-8-20261027','leaf-sampler1-20261027']:
 for p in Path('evidence',folder).glob('*.lean'):files[p.stem]=p
for p in Path('evidence/leaf-p6-1-20261027').glob('LPa_L*/sources/LPa_generated/*.lean'):files.setdefault(p.stem,p)
seen=set();plan=[]
def visit(m):
 if m in seen or m in h['objects'] or m.startswith(('Aeneas','Mathlib','Std','Lean','Init','Batteries')):return
 seen.add(m);p=files.get(m);s=h['sources'].get(m)
 if s is None:
  if p is None:raise RuntimeError(m)
  s=p.read_text()
 for line in s.splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
 plan.append({'module':m,'repository_source':str(p) if p else None,'host_source':m+'.lean' if m in h['sources'] else None})
visit('LPg_Scanners');visit('LPc_TailTransport')
(E/'LPl_inherited-plan.json').write_text(json.dumps(plan,indent=2)+'\n');print(json.dumps(plan,indent=2))
