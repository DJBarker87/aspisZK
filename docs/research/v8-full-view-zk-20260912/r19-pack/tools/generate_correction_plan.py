#!/usr/bin/env python3
"""Reproduce fixed T163 signed-operator tables from the retained model inventory.
The real staged ORDER must separately pass check_stage_inventory.py.
"""
from pathlib import Path
from collections import Counter,defaultdict
import json,re,ast
root=Path(__file__).resolve().parents[1]
s=(root/'tests/model.hpp').read_text()
masks=ast.literal_eval('['+re.search(r'MASKS\[64\]=\{([^}]+)',s)[1]+']')
inactive=lambda r:not(masks[r//16]>>(r%16)&1)
pads=[r for r in range(912) if r%16>=13 and inactive(r)][:89]
order=list(range(1024));order[:89]=pads
missing=iter(j for j in range(89) if j not in pads)
for r in pads:
 if r>=89:order[r]=next(missing)
support=[j for j in range(1024) if order[j]!=j]
assert len(support)==163 and sorted(order)==list(range(1024)) and order[1023]==1023
plans={}
for typ in ['normal','carry']:
 m=defaultdict(Counter)
 for j in support:
  if typ=='carry' and j%16>=3:continue
  r=order[j];m[r//16,j//16][r%16,j%16]+=1;m[j//16,j//16][j%16,j%16]-=1
 m={k:dict((ls,v) for ls,v in cs.items() if v) for k,cs in m.items()};m={k:v for k,v in m.items() if v}
 pairs=sorted({ls for cs in m.values() for ls in cs});terms=[];blocks=[]
 for (sh,dh),cs in sorted(m.items()):
  start=len(terms)
  for ls,v in sorted(cs.items()):
   assert v in (-1,1);terms.append([pairs.index(ls),v])
  blocks.append([sh,dh,start,len(terms)])
 rebuilt=Counter();expected=Counter()
 for sh,dh,start,end in blocks:
  for idx,v in terms[start:end]:
   sl,dl=pairs[idx];rebuilt[16*sh+sl,16*dh+dl]+=v
 for j in support:
  if typ=='carry' and j%16>=3:continue
  expected[order[j],j]+=1;expected[j,j]-=1
 assert {k:v for k,v in rebuilt.items() if v}=={k:v for k,v in expected.items() if v}
 plans[typ]={'pairs':pairs,'blocks':blocks,'terms':terms}
meta={'source_commit':'77fb78727c8b880b7c029828ad93083ff854f7f6','scope':'Model inventory; check the actual staged ORDER before using these tables','order':order,'support':support,'plans':plans,'signed_operator_equality_checked_over_integers':True,'single_tensor_reference_logical_products':408,'single_tensor_candidate_logical_products':sum(len(p['pairs'])+len(p['blocks']) for p in plans.values())+64,'cu_measured':False}
(root/'evidence/correction_plan.json').write_text(json.dumps(meta,indent=2)+'\n')
cpp='// Generated signed fixed-map correction plan.\n';rust='// Generated fixed T163 plan: actual stage inventory check required.\n'
for name,p in plans.items():
 for kind in ['pairs','blocks','terms']:
  rows=p[kind];width=len(rows[0]);ident=(name+'_'+kind).upper()
  cpp+=f'const int {ident}[{len(rows)}][{width}] = '+'{'+','.join('{'+','.join(map(str,row))+'}' for row in rows)+'};\n'
  rust+=f'pub const {ident}: [[i16; {width}]; {len(rows)}] = '+repr([list(row) for row in rows])+';\n'
(root/'tests/correction_tables.hpp').write_text(cpp);(root/'src/correction_tables.rs').write_text(rust)
print(json.dumps({'signed_operator_equality':True,'support':len(support),'single_tensor_reference_products':408,'single_tensor_candidate_products':meta['single_tensor_candidate_logical_products']}))
