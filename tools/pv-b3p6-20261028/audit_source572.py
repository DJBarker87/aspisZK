"""Derive a focused NEP_Driver audit of every new top theorem, with no skipped root."""
from pathlib import Path
import re,json,hashlib,argparse
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
modules=['PV_B3P_ResidualSource572227','PV_B3P_ResidualFamily572227','PV_B3P_FixedIndex572227']+[f'PV_B3P_FixedIndices572227_{j:02d}'for j in range(7)]+['PV_B3P_StepSource572227','PV_B3P_StepFamily572227','PV_B3P_ResultSource572227']
roots=[]
for m in modules:
 s=(D/'lean'/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots.extend(ns+'.'+r for r in re.findall(r'^#print axioms (\S+)',s,re.M))
assert len(roots)==len(set(roots))==405
reference=(D/'lean/PV_B3P_NEPCohort571227.lean').read_text()
s=reference.replace('b3p6_cohort571','b3p6_cohort572')
s=re.sub(r'  let modules := #\[.*?\]\n  let roots := #\[.*?\]\n', '  let modules := #[\n    '+',\n    '.join('`'+m for m in modules)+']\n  let roots := #[\n    '+',\n    '.join('`'+r for r in roots)+']\n',s,flags=re.S)
mask=lambda t:re.sub(r'  let modules :=.*?  let env ←','  let env ←',t,flags=re.S).replace('b3p6_cohort571','b3p6_cohort572')
assert mask(s)==mask(reference)
pin=json.loads((R/'NEP-PROVENANCE-D571.json').read_text());walker=(D/'lean/PV_B3P_NEPWalker569227.lean').read_bytes();assert hashlib.sha256(walker).hexdigest()==pin['walker_sha256']
x=dict(pin,driver='PV_B3P_NEPCohort572227',driver_reference='PV_B3P_NEPCohort571227',requested_root_count=len(roots),roots=roots,modules=modules,scope='All 405 new top theorem reachable graphs only; unchanged endpoint/source-cone roots reuse D571, not a full release replay',audit_attempt=None,complete_requested_graphs=False)
for p,t in {D/'lean/PV_B3P_NEPCohort572227.lean':s,R/'NEP-PROVENANCE-D572.json':json.dumps(x,indent=2)+'\n'}.items():
 if args.check:assert p.read_text()==t,p
 else:p.write_text(t)
print(json.dumps(dict(modules=len(modules),roots=len(roots),driver_unchanged_except_arrays_and_label=True,check=args.check)))
