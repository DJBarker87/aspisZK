from pathlib import Path
import json,re
L=Path('evidence/pv-lib-20261107/lane-SPEC')
modules=['PV_LIB_SPEC_'+name for name in ['NativeRuntime','ResourceHistory','ConcreteCaptures','ConcreteEntry','BoundRuntime','HistoryInvariant','JointPremises','ControlRuntime','ControlHistory','ControlJoint']]
roots=[]
for m in modules:
 stack=[]
 for line in Path('lean',m+'.lean').read_text().splitlines():
  ns=re.match(r'^namespace\s+(\S+)',line); end=re.match(r'^end\s+(\S+)',line)
  dec=re.match(r'^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|theorem)\s+([\w\'.]+)',line)
  if ns:stack.append(ns[1])
  elif end:
   assert stack.pop()==end[1]
  elif dec:roots.append('.'.join(stack+[dec[1]]))
 assert not stack
base=Path('lean/PV_LIB_SPEC_RawAuditSession5W3.lean').read_text()
a=base.index('  let (modules, roots) :=');b=base.index('  let env ← importModules',a)
s=base[:a]+'  let (modules, roots) :=\n    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])\n'+base[b:]
name='PV_LIB_SPEC_RawAuditSession6'
Path('lean',name+'.lean').write_text(s)
(L/'SESSION6_RAW_ROOTS.json').write_text(json.dumps({'driver':name,'modules':modules,'roots':roots,'count':len(roots)},indent=2)+'\n')
print(len(roots))
