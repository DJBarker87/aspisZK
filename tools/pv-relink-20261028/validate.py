"""Read-only final evidence checks; no compiler/solver invocation."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028'
rows=['V178','V179','V182','V195','V233'];errors=[];checks={}
for row in rows:
 r=json.loads((E/row/'row.json').read_text());b=json.loads((E/(row+'-binding.json')).read_text())
 if b['evidence_class']!='structural (K-1 substitute)':errors.append([row,'class'])
 if r['after']['status']!='RELINKED at prior candidate scope':errors.append([row,'pending'])
 n=E/r['native_receipt'];j=json.loads(n.read_text());log=(n.parent/'output.log').read_text()
 if j['exit']!=0 or 'finite validation:' not in log or 'no disagreement' not in log:errors.append([row,'native'])
 if 'Kani' in str(j['target']) or 'cargo kani' in str(j['target']):errors.append([row,'solver invocation'])
 for p in (E/row).glob('suspended-*-*.txt'):
  if not p.read_bytes():errors.append([row,'missing historical output',str(p)])
 checks[row]=dict(binding_sha256=hashlib.sha256((E/(row+'-binding.json')).read_bytes()).hexdigest(),native_receipt=str(n.relative_to(E)),closing_theorem=r['closing_theorem'],before=r['before'],after=r['after'])
t=json.loads((E/'attempts.json').read_text());ids=[x['id'] for x in t]
assert len(ids)==len(set(ids)) and all(43700<=x<=43799 for x in ids)
assert sum(x.get('charged',False) for x in t)<=100
for x in t:
 p=E/str(x['id'])/'receipt.json'
 if not x.get('charged'):continue
 j=json.loads(p.read_text())
 if j['exit']==0:
  for a in j['axioms']:
   if any(z not in ['propext','Classical.choice','Quot.sound'] for z in re.findall(r'axioms: \[([^]]*)\]',a)[0].split(', ')) if 'axioms: [' in a else False:errors.append([x['id'],'axioms',a])
  if j['swap']!='0':errors.append([x['id'],'swap'])
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RL_*.lean'):
 s=re.sub(r'/\-.*?\-/|--[^\n]*','',p.read_text(),flags=re.S)
 if re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b|^import .*\bXR\w*',s,re.M):errors.append([str(p),'forbidden'])
diff=subprocess.check_output(['git','diff','--name-only','82566acdfb','HEAD'],cwd=R,text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in diff)
checks.update(lean_charged=sum(x.get('charged',False) for x in t),kani=0,ids=ids,endpoint_premises_removed=0,trust_added=0,target='not yet established')
j=dict(ok=not errors,errors=errors,checks=checks);(E/'validation.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(ok=j['ok'],errors=errors,lean=checks['lean_charged'],kani=0)));raise SystemExit(bool(errors))
