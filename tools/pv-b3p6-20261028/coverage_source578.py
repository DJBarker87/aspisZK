"""Reconcile the SAME 528 sites; local certificates are not endpoint closure."""
from pathlib import Path
import argparse,copy,json
R=Path('evidence/pv-b3p6-20261028/resume18')
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
x=copy.deepcopy(json.loads((R/'SOURCE-COVERAGE-D572.json').read_text()));extra={}
records=['INITIALIZER-SOURCE','FRAME-INDICES','SLICE-SOURCE','DOMINATED-INDICES','SPECIALIZED-INDICES','RANGE-INDICES','WINDOW-INDICES','SUB-PANIC-SOURCE']
for name in records:
 f=name+'-D578.json';v=json.loads((R/f).read_text())
 for row in v['rows']:
  key=row['instance'],row['statement'];assert key not in extra,key
  extra[key]=dict(kind=v['evidence_class'],lemma=row['lemma'],record=f)
for pattern,group in x['groups'].items():
 retained=[]
 for row in group['remaining']:
  key=row['instance'],row['statement']
  if key in extra:
   row['local_source_certificates']=[extra.pop(key)]
   row['source_state_binding']='SCRIPT-CHECKED own-1 source projection/private scalar frame; exact scope in cited record'
   row['actual_reachable_guard_proof']='Lean prefix-event guard; whole endpoint entry, native pointer realization and dictionary composition OPEN'
   group['certified'].append(row)
  else:retained.append(row)
 group['remaining']=retained
 x['counts'][pattern]=dict(total=len(group['certified'])+len(retained),local_source_state_certificates=len(group['certified']),remaining_local_source_state_certificates=len(retained))
assert not extra,extra
assert sum(v['local_source_state_certificates']for v in x['counts'].values())==357
assert sum(v['total']for v in x['counts'].values())==528
x['scope']='Local source scalar projections and guard certificates; includes structural frame bindings and generated named Lean applications. Pointer validity, partial initialization, restoration, drops, globals, helper closure and actual dictionary composition remain OPEN.'
out=R/'SOURCE-COVERAGE-D578.json';s=json.dumps(x,indent=2)+'\n'
if a.check:assert out.read_text()==s
else:out.write_text(s)
print(json.dumps(dict(local_certified=357,remaining=171,counts=x['counts'],check=a.check)))
