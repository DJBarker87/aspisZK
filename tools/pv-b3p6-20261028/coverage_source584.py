"""Account for prepared local scalar certificates; compiles/raw audit are a separate gate."""
from pathlib import Path
import json,copy,argparse
R=Path('evidence/pv-b3p6-20261028/resume18');p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
x=copy.deepcopy(json.loads((R/'SOURCE-COVERAGE-D580.json').read_text()));extra={}
for filename in ['NORMALIZED-INDICES-D583','COMPUTED-INDICES-D583','METADATA-INDICES-D584','CALLBACK-INDICES-D584']:
 data=json.loads((R/(filename+'.json')).read_text())
 for row in data['rows']:
  key=row['instance'],row['statement'];assert key not in extra
  extra[key]=dict(row=row,evidence_class=data['evidence_class'],record=filename+'.json')
assert len(extra)==94
for pattern,group in x['groups'].items():
 remain=[]
 for row in group['remaining']:
  key=row['instance'],row['statement']
  if key in extra:
   cert=extra.pop(key);row['source_state_binding']=cert['evidence_class'];row['actual_reachable_guard_proof']='Named kernel theorem application on checked scalar source-event projection; no guard input; native memory/caller association retained'
   row['local_source_certificates']=[dict(kind=cert['evidence_class'],lemma=cert['row']['lemma'],record=cert['record'])];group['certified'].append(row)
  else:remain.append(row)
 group['remaining']=remain;x['counts'][pattern]=dict(total=len(group['certified'])+len(remain),local_source_state_certificates=len(group['certified']),remaining_local_source_state_certificates=len(remain))
assert not extra and sum(v['local_source_state_certificates']for v in x['counts'].values())==459
out=R/'SOURCE-COVERAGE-D584.json';s=json.dumps(x,indent=2)+'\n'
if a.check:assert out.read_text()==s
else:out.write_text(s)
print(json.dumps(dict(local_prepared=459,remaining=69,requires='all six new modules compile and97-root NEP audit',check=a.check)))
