"""Account for prepared mappings; compile and raw audit are a separate gate."""
from pathlib import Path
import json,copy,argparse
R=Path('evidence/pv-b3p6-20261028/resume18');p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();x=copy.deepcopy(json.loads((R/'SOURCE-COVERAGE-D587.json').read_text()));extra={}
records=['RANGE-ARITHMETIC','TABLE-INDICES','STABLE-INDICES','COUNTDOWN-INDICES','CALLER-INDICES','PREWEIGHTED-INDICES','FOLD-INDICES','ROW-INDICES','EXPAND-INDICES']
for record in records:
 data=json.loads((R/(record+'-D592.json')).read_text())
 for row in data['rows']:
  key=row['instance'],row['statement'];assert key not in extra;extra[key]=dict(row=row,record=record+'-D592.json',evidence_class=data['evidence_class'])
assert len(extra)==44
for pattern,group in x['groups'].items():
 remain=[]
 for row in group['remaining']:
  key=row['instance'],row['statement']
  if key in extra:
   cert=extra.pop(key);row['source_state_binding']=cert['evidence_class'];row['actual_reachable_guard_proof']='Named kernel theorem on checked scalar source-event projection; native memory and whole caller association retained'
   row['local_source_certificates']=[dict(kind=cert['evidence_class'],lemma=cert['row']['lemma'],record=cert['record'])];group['certified'].append(row)
  else:remain.append(row)
 group['remaining']=remain;x['counts'][pattern]=dict(total=len(group['certified'])+len(remain),local_source_state_certificates=len(group['certified']),remaining_local_source_state_certificates=len(remain))
assert not extra and sum(v['local_source_state_certificates']for v in x['counts'].values())==528
x['validation_gate']='PREPARED count; consume only with successful focused compiles and raw96-root NEP audit in verification-summary-D592.json'
residual={}
for pattern,group in x['groups'].items():
 byid={}
 for row in group['remaining']:
  fid=int(row['instance'].split(':')[0]);gg=byid.setdefault(fid,dict(function_id=fid,sites=0,instances=set(),statements=set(),rows=[]));gg['sites']+=1;gg['instances'].add(row['instance']);gg['statements'].add(row['statement']);gg['rows'].append(row)
 for gg in byid.values():gg['instances']=len(gg['instances']);gg['statements']=sorted(gg['statements'])
 residual[pattern]=list(byid.values())
outputs={R/'SOURCE-COVERAGE-D592.json':x,R/'REMAINING-GUARDS-D592.json':dict(remaining=0,status='after44 new prepared mappings; compile/audit validation separate',groups=residual)}
for p,data in outputs.items():
 s=json.dumps(data,indent=2)+'\n'
 if a.check:assert p.read_text()==s,p
 else:p.write_text(s)
print(json.dumps(dict(local_prepared=528,remaining=0,requires='all16 modules compile and96-root raw NEP audit',check=a.check)))
