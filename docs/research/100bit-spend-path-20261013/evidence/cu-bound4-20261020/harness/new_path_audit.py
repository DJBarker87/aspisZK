"""Audit every executed branch and loop in the refactored verifier paths."""
import json,sys,hashlib,struct
from pathlib import Path
H=Path(sys.argv[1]);A=H/'analysis';rules=json.loads((H/'harness/rules.json').read_text());out={}
fnparts=['candidate3tx1','candidate10tx2_common','candidate12batch_merkle','accumulate_batched_with_node','BatchedWeights','QueryGeometry','finish_relation','finish_query_dot']
for role in ['stage1','stage2']:
 d=json.loads((A/f'{role}.json').read_text());s=json.loads((A/'sites-per-variant.json').read_text());vs=[x for x in s if x['role']==role];branches=[];loops=[]
 for i,b in enumerate(d['branches']):
  if not any(p in b['function'] for p in fnparts) or not any(t['counts'][i] for t in d['traces']):continue
  cls=[dict(variant=x['variant'],**y) for x in vs for y in x['sites'] if y['addr']==b['addr'] and y['cls']!='loop-in-arm' and y['cls']!='loop']
  assert cls and all(x['rule']!='R?' for x in cls)
  branches.append(dict(addr=b['addr'],function=b['function'],classification_per_variant=[{k:x[k] for k in ['variant','rule','residual','count_w','taken_w','notes'] if k in x} for x in cls]))
 for l in d['loops']:
  if not any(p in l['function'] for p in fnparts) or not any(t[0] for t in l['per_trace']):continue
  rr=[r for r in rules['loop_caps'] if r['role'] in [role,'*'] and l['header'] in r.get('addr',[])]
  assert rr,(role,l['header'],l['function'])
  assert all(max(l['max_trip_per_entry'])<=r['N'] for r in rr if isinstance(r['N'],int)),(role,l['header'],l['max_trip_per_entry'])
  loops.append(dict(header=l['header'],function=l['function'],source_caps=rr,max_observed_per_entry=max(l['max_trip_per_entry'])))
 first=[]
 for addr in ['0x29c80','0x2ae68','0x2c0e8']:
  k=next(i for i,b in enumerate(d['branches']) if b['addr']==addr)
  assert all(t['counts'][k]==1 and t['taken'][k]==0 for t in d['traces'])
  first.append(dict(addr=addr,traces=len(d['traces']),count_each=1,taken_each=0,reason='F-FIRST-KEY-NONEMPTY in rules.json; source + ELF argument, not inferred from counts'))
 out[role]=dict(executed_branches=branches,executed_loops=loops,first_key_checks=first,source='b2727acd3 frozen')
(H/'new-path-audit.json').write_text(json.dumps(out,indent=1)+'\n');print({r:dict(branches=len(x['executed_branches']),loops=len(x['executed_loops'])) for r,x in out.items()})
