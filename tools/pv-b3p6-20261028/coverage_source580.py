"""Extend the SAME528-site account by the two metadata-bound assertions."""
from pathlib import Path
import argparse,copy,json
R=Path('evidence/pv-b3p6-20261028/resume18');p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
x=copy.deepcopy(json.loads((R/'SOURCE-COVERAGE-D579.json').read_text()));m=json.loads((R/'METADATA-SOURCE-D580.json').read_text());extra={(r['instance'],r['statement']):r for r in m['rows']}
for pattern,group in x['groups'].items():
 remain=[]
 for row in group['remaining']:
  key=row['instance'],row['statement']
  if key in extra:
   cert=extra.pop(key);row['source_state_binding']='SCRIPT-CHECKED own-1 literal array-to-slice metadata at ALL captured incoming calls, complete store prefix including moves and scalar stack references'
   row['actual_reachable_guard_proof']='Lean local-store interpreter proves assertion condition true for every prior store, using actual source metadata7/7 or4; no guard input'
   row['local_source_certificates']=[dict(kind=m['evidence_class'],lemma=cert['lemma'],record='METADATA-SOURCE-D580.json')];group['certified'].append(row)
  else:remain.append(row)
 group['remaining']=remain;x['counts'][pattern]=dict(total=len(group['certified'])+len(remain),local_source_state_certificates=len(group['certified']),remaining_local_source_state_certificates=len(remain))
assert not extra and sum(v['local_source_state_certificates']for v in x['counts'].values())==365
out=R/'SOURCE-COVERAGE-D580.json';s=json.dumps(x,indent=2)+'\n'
if a.check:assert out.read_text()==s
else:out.write_text(s)
print(json.dumps(dict(local_certified=365,remaining=163,check=a.check)))
