from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
objs={str(p.relative_to(root)).removesuffix('.olean').replace('/','.') for root in [B,B/'objects'] for p in root.rglob('*.olean') if len(p.relative_to(root).parts)<4}
sources={}
for p in B.rglob('*.lean'):
 if len(p.relative_to(B).parts)>3:continue
 m=str(p.relative_to(B)).removesuffix('.lean').replace('/','.')
 if m.startswith('objects.'):continue
 sources[m]=[x for l in p.read_text().splitlines() if l.startswith('import ') for x in l[7:].split()]
print(json.dumps({'objects':sorted(objs),'imports':sources}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 - <<\'PYREMOTE\'\n'+code+'\nPYREMOTE'],capture_output=True,text=True,check=True)
h=json.loads(r.stdout); (E/'LPh_host-inventory.json').write_text(json.dumps(h,indent=2)+'\n')
avail=set(h['objects']); seen=set(); order=[]; missing={}
def visit(m):
 if m in seen or m.startswith(('Aeneas','Mathlib','Std','Lean','Init','Batteries')):return
 seen.add(m); p=Path('lean')/(m.replace('.','/')+'.lean')
 deps=h['imports'].get(m)
 if deps is None and p.exists():deps=[x for l in p.read_text().splitlines() if l.startswith('import ') for x in l[7:].split()]
 for d in deps or []:visit(d)
 if m not in avail:
  missing[m]={'module':m,'repository_source':str(p),'exists':p.exists(),'imports':deps}
  order.append(m)
for m in ['FIo_M31MulBridge','ExtractedCurrentReducer','FJf_RawReference','FIo_WideMulValues']:visit(m)
plan=[missing[m] for m in order];(E/'LPh_inherited-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(plan,indent=2))
