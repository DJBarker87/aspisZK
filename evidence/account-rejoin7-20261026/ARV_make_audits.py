"""Generate distinct per-theorem statement audits; no proof/build infrastructure."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent
items=[]
for f in sorted((R/'lean').glob('ARV_*.lean')):
    s=f.read_text(); ns=re.search(r'^namespace (\S+)',s,re.M)
    if not ns:continue
    for name in re.findall(r'^theorem (\w+)',s,re.M):items.append((f.stem,ns.group(1)+'.'+name))
assert len(items)==48,len(items)
plan=[]
for n,(mod,name) in enumerate(items,51):
    audit='ARV_Statement_'+str(n)
    text=f'''import {mod}
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140
-- Complete binder/trust-scope audit only; zero deployed premise-removal credit.
#check @{name}
#print axioms {name}
'''
    (R/'lean'/(audit+'.lean')).write_text(text)
    plan.append(dict(attempt=n,module=audit,theorem=name,owner_module=mod,kind='distinct complete statement / trust-scope audit'))
(P/'ARV_AUDIT_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
(P/'ARV_THEOREMS.json').write_text(json.dumps(items,indent=2)+'\n')
