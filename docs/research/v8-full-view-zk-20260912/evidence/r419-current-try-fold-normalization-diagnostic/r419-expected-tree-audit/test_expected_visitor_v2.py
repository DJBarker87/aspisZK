#!/usr/bin/env python3
"""Synthetic tests for binder-aware expected-delta visitor v2."""
import importlib.util, json
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('expected',HERE/'expected_from_original_v2.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
checks=[]
def rejects(label,fn,needle):
 try:fn()
 except ValueError as e:
  assert needle in str(e),(label,str(e));checks.append({'case':label,'result':'rejected','message':str(e)})
 else:raise AssertionError(f'{label} unexpectedly accepted')
assert m.reindex_proj({'TypeVar':{'Bound':[4,8]}},'Free',2)=={'TypeVar':{'Bound':[4,8]}}
assert m.reindex_proj({'TypeVar':{'Free':8}},'Bound',0)=={'TypeVar':{'Free':8}}
checks.append({'case':'typevar namespace-safe reindex','result':'passed'})
proj={'type':{'TypeVar':{'Bound':[0,0]}},'region':{'Var':{'Bound':[0,1]}},'constant':{'Var':{'Bound':[0,2]}},'clause':{'Clause':{'Bound':[0,3]}}}
lifted=m.lift_proj(proj,2)
assert [lifted['type']['TypeVar']['Bound'],lifted['region']['Var']['Bound'],lifted['constant']['Var']['Bound'],lifted['clause']['Clause']['Bound']]==[[2,0],[2,1],[2,2],[2,3]]
checks.append({'case':'insertion lifts type/region/const/clause indices','result':'passed'})
projection={'Literal':'I32'}
tree={'params':{'constraint':{'regions':[],'skip_binder':{'ty':{'TypeVar':{'Bound':[2,0]}}}}},'skip_binder':{'body':{'TypeVar':{'Bound':[1,0]}}},'kind':'TraitMethod'}
ops=[]; old_trace=m.trace;m.trace=ops
mapped=m.map_vars(tree,'Bound',0,projection)
m.trace=old_trace
assert mapped['params']['constraint']['skip_binder']['ty']==projection
assert mapped['skip_binder']['body']==projection
assert len(ops)==2
checks.append({'case':'Binder params and value both increment depth; enclosing method binder excluded','result':'passed'})
rejects('removed-binder escape',lambda:m.transform_bound_refs({'TypeVar':{'Bound':[0,0]}},-1),'escapes')
nested={'params':{'x':{'TypeVar':{'Bound':[1,5]}}},'skip_binder':{'x':{'Var':{'Bound':[1,6]}}}}
l=m.lift_proj(nested,1)
assert l['params']['x']['TypeVar']['Bound']==[2,5] and l['skip_binder']['x']['Var']['Bound']==[2,6]
checks.append({'case':'nested Binder params/value lifting','result':'passed'})
(HERE/'expected-visitor-v2-negative-cases.json').write_text(json.dumps({'classification':'synthetic visitor tests only; no candidate input and no semantic acceptance','cases':checks},indent=2)+'\n')
print(json.dumps({'case_count':len(checks),'receipt':str(HERE/'expected-visitor-v2-negative-cases.json')},indent=2))
