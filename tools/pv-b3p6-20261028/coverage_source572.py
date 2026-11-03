"""Account for local certificates without promoting them to endpoint closure."""
from pathlib import Path
import json,collections,argparse
R=Path('evidence/pv-b3p6-20261028/resume18')
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
g=json.loads((R/'PANIC-PATTERN-GROUPS-D571.json').read_text());cert={}
def add(instance,statement,kind,lemma,record):
 key=(instance,statement);cert.setdefault(key,[]).append(dict(kind=kind,lemma=lemma,record=record))
for x in json.loads((R/'FIXED-INDICES-D572.json').read_text())['rows']:add(x['instance'],x['statement'],'fixed-array source constant',x['lemma'],'FIXED-INDICES-D572.json')
for x in json.loads((R/'SOURCE-GUARDS-D572.json').read_text())['instances']:add(x['instance'],x['statement'],'complete residual-arm local state','PV_B3P_ResidualFamily572227.family_certificate','SOURCE-GUARDS-D572.json')
for x in json.loads((R/'STEP-SOURCE-GUARDS-D572.json').read_text())['instances']:add(x['instance'],x['statement'],'guarded source checked-successor event',x['lemma'],'STEP-SOURCE-GUARDS-D572.json')
# Result residuals are withheld until deployed/extractor source parity is checked.
result=json.loads((R/'RESULT-SOURCE-GUARDS-D572.json').read_text())if (R/'RESULT-SOURCE-GUARDS-D572.json').exists()else None
if result and (R/'RESULT-SOURCE-PARITY-D572.json').exists():
 assert all(x['tokens_identical']for x in json.loads((R/'RESULT-SOURCE-PARITY-D572.json').read_text())['items'])
 for x in result['instances']:add(x['instance'],x['statement'],'typed uninhabited success carrier','PV_B3P_ResultSource572227.family_certificate','RESULT-SOURCE-GUARDS-D572.json')
for x in json.loads((R/'DISABLED-GATES-D571.json').read_text())['certificates']:
 for e in x['events']:add(x['instance'],e['statement'],'inherited literal-false source gate',x['lemma'],'DISABLED-GATES-D571.json')
counts={};out={}
for pattern,rows in g['groups'].items():
 covered=[];openrows=[]
 for row in rows:
  key=(row['instance'],row['statement']);copy=dict(row)
  if key in cert:
   copy['local_source_certificates']=cert.pop(key);copy['source_state_binding']='SCRIPT-CHECKED local source reflection; exact scope in cited record';copy['actual_reachable_guard_proof']='Lean local guard; full endpoint caller/dictionary application OPEN';covered.append(copy)
  else:openrows.append(copy)
 counts[pattern]=dict(total=len(rows),local_source_state_certificates=len(covered),remaining_local_source_state_certificates=len(openrows))
 out[pattern]=dict(certified=covered,remaining=openrows)
assert not cert,cert
assert sum(x['total']for x in counts.values())==528
x=dict(counts=counts,groups=out,scope='Local source-state reflection and guard certificates only. No claim of completed actual caller reachability, borrowed-memory semantics, opaque helper coverage or dictionary composition.',new_guard_hypotheses_added_to_endpoint=False,source_cone_complete=False,deployed_wrapper_discharged=False,premises_removed=[],premises_added=[],premises_weakened=[])
s=json.dumps(x,indent=2)+'\n';p=R/'SOURCE-COVERAGE-D572.json'
if args.check:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(counts=counts,check=args.check)))
