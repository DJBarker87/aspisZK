import json,sys
from pathlib import Path
E=Path(__file__).resolve().parent
mods=set(json.loads((E/'NBK_AVAILABLE_MODULES.json').read_text()))
for p in E.glob('NBK_L*/receipt.json'):
 x=json.loads(p.read_text())
 if x['exit_status']==0:
  cmd=x['command'];mods.add(cmd[cmd.index('-o')+1].split('/')[-1].removesuffix('.olean'))
missing=[];unknown=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 paths=[Path('lean')/(m.replace('.','/')+'.lean'),Path('docs/research/100bit-spend-path-20261013/lean')/(m.replace('.','/')+'.lean')]
 p=next((p for p in paths if p.is_file()),None)
 if p is None:
  if m not in mods and not m.startswith(('Init','Lean','Mathlib','Aeneas')):unknown.append(m)
  return
 for l in p.read_text().splitlines():
  if l.startswith('import '):
   for dep in l.split()[1:]:visit(dep)
 if m not in mods:missing.append([m,str(p)])
for m in sys.argv[1:]:visit(m)
x={'missing':missing,'unknown':unknown,'roots':sys.argv[1:]}
(E/'NBK_FULL_MISSING_PLAN.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x,indent=2))
