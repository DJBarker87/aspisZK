"""Resolve the exact tracked V265 project dependency closure before rebuilding it."""
from pathlib import Path
import re,json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028'
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
seen={};order=[]
def go(m):
 if m in seen:return
 p='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
 b=git('show','HEAD:'+p)
 deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 seen[m]=dict(path=p,blob=git('rev-parse','HEAD:'+p).decode().strip(),sha256=hashlib.sha256(b).hexdigest(),imports=deps,authority='h5 tracked own HEAD; subject to higher-priority absence census below')
 for dep in deps:
  if dep.startswith('R1Z.'):go(dep)
 order.append(m)
go('R1Z.PV_RDCD3_V265Inverse')
checks={}
for ref in ['evidence/envj-rebuild-20261026/EJR_final-inventory.json','docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json']:
 raw=git('show','research:'+ref);j=json.loads(raw);hits=[]
 def visit(x):
  if isinstance(x,dict):
   for k in ['module','name']:
    if isinstance(x.get(k),str) and x[k].replace('/','.') in seen:hits.append(x)
   for v in x.values():visit(v)
  elif isinstance(x,list):
   for v in x:visit(v)
 visit(j)
 assert not hits,(ref,hits)
 checks[ref]=dict(blob=git('rev-parse','research:'+ref).decode().strip(),sha256=hashlib.sha256(raw).hexdigest(),hits=hits)
(E/'v265-source-resolution.json').write_text(json.dumps(dict(revision=git('rev-parse','HEAD').decode().strip(),modules=seen,compile_order=order,higher_priority_absence=checks,object_reuse='none: prior rdcd objects removed by prior cleanup'),indent=2)+'\n')
print('\n'.join(order))
