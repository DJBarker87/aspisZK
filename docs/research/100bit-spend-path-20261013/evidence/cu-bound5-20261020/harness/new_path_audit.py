"""Supplement the complete branch audit with every candidate-changed function.
Positional L0 is reported as the reviewed empirical method, never a source cap.
"""
import json,sys
from pathlib import Path
H=Path(sys.argv[1]);A=H/'analysis';rules=json.loads((H/'harness/rules.json').read_text());out={}
fnparts=['candidate3tx1','candidate10tx2_common','candidate12batch_merkle','candidate14canonical_scan','accumulate_batched_with_node','BatchedWeights','QueryGeometry','finish_relation','finish_query_dot','verifier10checkpoint','verifier6echeck','weights','r1_semantic']
spv=json.loads((A/'sites-per-variant.json').read_text())
for role in ['stage1','stage2']:
 d=json.loads((A/f'{role}.json').read_text());lm=json.loads((A/f'lines-{role}.json').read_text());vs=[x for x in spv if x['role']==role];branches=[];loops=[]
 for i,b in enumerate(d['branches']):
  if not any(p in b['function'] for p in fnparts) or not any(t['counts'][i] for t in d['traces']):continue
  cls=[dict(variant=x['variant'],**y) for x in vs for y in x['sites'] if y['addr']==b['addr'] and y['cls'] not in ['loop-in-arm','loop']]
  assert cls and all(x['rule']!='R?' for x in cls),(role,b['addr'])
  branches.append(dict(addr=b['addr'],function=b['function'],frames=lm.get(b['addr'],{}).get('frames',[]),classification_per_variant=[{k:x[k] for k in ['variant','rule','residual','count_w','taken_w','notes'] if k in x} for x in cls]))
 for l in d['loops']:
  if not any(p in l['function'] for p in fnparts) or not any(t[0] for t in l['per_trace']):continue
  rr=[r for r in rules['loop_caps'] if r['role'] in [role,'*'] and l['header'] in r.get('addr',[])]
  cls=[dict(variant=x['variant'],**y) for x in vs for y in x['sites'] if y['addr']==l['header'] and y['cls']=='loop']
  assert cls and all(x['rule'] in ['L0','L1'] for x in cls),(role,l['header'])
  assert all(x['rule']=='L0' or rr for x in cls),(role,l['header'])
  assert all(max(l['max_trip_per_entry'])<=r['N'] for r in rr if isinstance(r['N'],int)),(role,l['header'],l['max_trip_per_entry'])
  loops.append(dict(header=l['header'],function=l['function'],frames=lm.get(l['header'],{}).get('frames',[]),source_caps=rr,max_observed_per_entry=max(l['max_trip_per_entry']),classification_per_variant=cls))
 first=[]
 for rule in rules['exclusions']:
  if rule['id']!='F-FIRST-KEY-NONEMPTY':continue
  for addr in rule['addr']:
   k=next(i for i,b in enumerate(d['branches']) if b['addr']==addr)
   assert all(t['counts'][k]==1 and t['taken'][k]==0 for t in d['traces'])
   first.append(dict(addr=addr,traces=len(d['traces']),count_each=1,taken_each=0,source_rule=rule))
 out[role]=dict(executed_branches=branches,executed_loops=loops,first_key_checks=first,source='c16e59e77 candidate',L0_label='positional under reviewed empirical method, not a formal trip-cap proof')
(H/'new-path-audit.json').write_text(json.dumps(out,indent=1)+'\n');print({r:dict(branches=len(x['executed_branches']),loops=len(x['executed_loops'])) for r,x in out.items()})
