"""Find unchanged prerequisites of the adopted LPn model in the coherent cache.
No source edits, shared writes, or infrastructure changes. Builds are separate
admitted invocations and count against this job's Lean budget.
"""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
S='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
# Prefer accepted source snapshots over older experiments.
index={}
for root in ['lean','docs/research/100bit-spend-path-20261013/lean','evidence/leaf-p6-10-20261027','evidence/leaf-p6-12-20261027']:
 for p in Path(root).glob('*.lean'):index[p.stem]=p
seen=set();plan=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 r=subprocess.run(['ssh','dombarker@100.108.41.90',f'test -f {S}/{m.replace(chr(46),chr(47))}.olean -o -f {S}/objects/{m.replace(chr(46),chr(47))}.olean'],capture_output=True)
 if r.returncode==0:return
 if m not in index:raise RuntimeError('missing unchanged source '+m)
 p=index[m]
 for l in p.read_text().splitlines():
  if l.startswith('import '):
   for dep in l[7:].split():visit(dep)
 plan.append({'module':m,'repository_source':str(p)})
visit('LPn_Kit_DecodeModels')
(E/'LPo_inherited-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(plan,indent=2))
