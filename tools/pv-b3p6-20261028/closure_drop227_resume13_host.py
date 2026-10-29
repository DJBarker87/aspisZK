"""Fail-closed structural check of every precise Drop in the refused source cone.
No LLBC/output is rewritten and the extractor is not bypassed or rerun.
"""
from pathlib import Path
import json,hashlib,re
from run import H
p=H/'source-prepared-resume12/PV_B3P_SourcePrepared12.llbc';raw=p.read_bytes();x=json.loads(raw);t=x['translated'];hv={};drops=[]
def walk(v):
 if isinstance(v,dict):
  if 'HashConsedValue'in v:
   i,w=v['HashConsedValue'];hv[i]=w
  for w in v.values():walk(w)
 elif isinstance(v,list):
  for w in v:walk(w)
walk(x)
def find(v,owner,path):
 if isinstance(v,dict):
  for k,w in v.items():
   if k=='Drop':drops.append(dict(owner=owner,path=path+[k],statement=w))
   find(w,owner,path+[k])
 elif isinstance(v,list):
  for i,w in enumerate(v):find(w,owner,path+[i])
for f in t['fun_decls']:
 if f:find(f,f['def_id'],[])
assert len(drops)==2,drops
for d in drops:
 assert d['owner']==139 and d['statement']['kind']=='Precise'
 assert d['statement']['fn_ptr']['kind']=={'Fun':{'Regular':154}}
 assert d['statement']['place']['ty']=={'Deduplicated':3409}
assert hv[3409]['Adt']['id']=={'Adt':37}
closure=t['type_decls'][37];assert closure['kind']=={'Struct':[]}
assert all(l['value']['size']==0 for l in closure['layout'])
glue=t['fun_decls'][154];stmts=glue['body']['Structured']['body']['statements'];kinds=[s['kind'] if isinstance(s['kind'],str)else next(iter(s['kind']))for s in stmts]
assert kinds==['StorageLive','Assign','StorageDead','Return'],kinds
assign=stmts[1]['kind']['Assign'][1];assert assign['Aggregate'][1]==[]
# Exact arithmetic closure body and owned callee, including every operation/order.
source=(H/'source/crates/aspis-core/src/field.rs').read_text();a=source.index('let reconstruct = |channels: [u64; 3]| {');a=source.index('{',a);b=a+1;depth=1
while depth:depth+=(source[b]=='{')-(source[b]=='}');b+=1
body=source[a:b]
owned=(H/'source/tools/pv-b3p6-20261028/v244/reference_field.rs').read_text();a2=owned.index('fn reconstruct_component(');a2=owned.index('{',a2);b2=a2+1;depth=1
while depth:depth+=(owned[b2]=='{')-(owned[b2]=='}');b2+=1
lex=lambda s:re.findall(r'\w+|[^\s]',re.sub(r'//[^\n]*','',s))
assert lex(body)==lex(owned[a2:b2]),(body,owned[a2:b2])
sha=lambda b:hashlib.sha256(b).hexdigest()
out=dict(evidence_class='structural (K-1 substitute); reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)',llbc_sha256=sha(raw),all_drop_sites=drops,closure_type=closure,drop_glue=glue,call_once_adapter=t['fun_decls'][139],drop_body_statement_kinds=kinds,drop_has_no_calls_or_branches=True,drop_fields=[],source_closure_body_sha256=sha(body.encode()),owned_reconstruct_body_sha256=sha(owned[a2:b2].encode()),body_token_identity=True,body_token_sha256=sha('\0'.join(lex(body)).encode()),model_theorems=['PV_B3P_Binding13227.reconstruct_cleanup_binding13','PV_B3P_Binding13227.reconstruct_drop_no_unwind13','PV_B3P_Binding13227.reconstruct_call_once_binding13'],unwind_routes={'call_unwind':'same empty drop then UnwindResume','drop_unwind':'UnwindTerminate unreachable because checked destructor is total/no-unwind'},compiler_generated_glue_boundary='V370 / pending owner D381,D386 retained',extractor_refusal_retained=True,no_generated_output_edited=True,whole_prepared_source_credit=False,remaining=['compose nested source range loops and accumulator/reconstruction','complete std and source model association'])
(H/'closure-drop-binding-resume13.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(drop_sites=2,empty_closure=True,source_closure_body_token_identical=True,whole_prepared_source_credit=False)))
