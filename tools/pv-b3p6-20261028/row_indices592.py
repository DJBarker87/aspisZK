"""Every actual row() caller: eighteen scalar expressions and the COPY_LINKS
endpoint row projection. The shift is the actual Usize shift, using the existing
row_high law; no row bound is assumed by the wrapper.
"""
from pathlib import Path
import json,lzma,hashlib,copy,argparse
from caller_observe592 import collect
from scalar_constants592 import constants
from source_normalize583 import normalize
from range_indices578 import seeds
from initializer_source578 import compact,find
from literal_tables592 import initialize
from computed_indices583 import render
from frame_indices578 import dicts
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def certify(ll,g,t):
 fs={f['def_id']:f for f in ll['fun_decls']if f}
 for fid in[61,70]:assert compact(fs[fid]['body'])==t[str(fid)]
 vs,_=constants(ll,fs);obs=[]
 for fid in[19,56,57,58]:
  b,changes=normalize(fs[fid]['body'],vs);sd,_=seeds(b)
  for r in collect(b,sd):
   if r['callee']!=61:continue
   domain=r['arguments'][1];assert domain and domain['limit']<=1024;obs.append(dict(caller_id=fid,normalizations=changes,**r))
 assert len(obs)==18 and len([e for e in g['edges']if e['callee_id']==61])==19
 links,events=initialize(fs[247]);rows=[[e['fields'][0]for e in q['fields'][3:]]for q in links['fields']];assert all(0<=v<1024 for rr in rows for v in rr)
 shift=compact(find(fs[61]['body'],7378)['kind']['Assign'][1]);assert shift['BinaryOp'][0]=={'Shr':'Wrap'}
 return obs,rows,events

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'ROW-TEMPLATE-D592.json').read_text());obs,values,events=certify(ll,g,t);controls={}
 for fid,sid,label in[(61,7378,'shift_changed'),(58,6779,'caller_row_changed'),(70,8316,'endpoint_row_changed')]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid);find(f['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_RowIndices592227';s='import PV_B3P_RowEvents592227\nimport PV_B3P_TableEvents592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for v in sorted({v for rr in values for v in rr}):s+=f'def row{v} : Fin 1024 := ⟨{v},by decide⟩\n'
 s+='def sourceRows : List (List (Fin 1024)) := [\n '+',\n '.join('['+','.join('row'+str(v)for v in rr)+']'for rr in values)+']\n';lemmas=[]
 for j,r in enumerate(obs+[None]):
  label=f'certificate_{j}';lemmas.append(name+'.'+label)
  if r is None:params='(link endpoint : Nat)';inputevent='PV_B3P_TableEvents592227.sourceEvent 1024 sourceRows link endpoint []'
  else:
   domain=r['arguments'][1];expr=copy.deepcopy(domain['expression']);range_limit=None
   for node in dicts(expr):
    if node.get('op')=='bounded'and node['input'][0]=='rangeItem':range_limit=node['limit'];node['input']=['snapshot','range_next',61]
   inputs=[];text=render(expr,inputs);params=('('+' '.join('input'+str(k)for k in range(len(inputs)))+' : Nat)')if inputs else''
   if range_limit is not None:
    assert len(inputs)==1;text=text.replace('input0','item.val');params='(handler : Str → Result Never) (current : Usize)';inputevent=f'PV_B3P_RangeComputedEvents592227.sourceEvent handler ⟨current,{range_limit}#usize⟩ (fun item => {text}) {1024-domain["limit"]} []'
   else:inputevent=f'PV_B3P_ArithmeticEvents583227.sourceEvent {text} {1024-domain["limit"]} []'
  s+=f'''/-- All-incoming scalar row observation, case {j}. -/
theorem {label} {{α : Type}} {params} (effects : List (Result Unit)) (observed : IndexState)
    (ran : PV_B3P_RowEvents592227.sourceEvent ({inputevent}) effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RowEvents592227.event_certificate ({inputevent}) effects observed ran normal first second
#print axioms {label}
'''
 inst=next(k for k,v in g['instances'].items()if v['id']==61);rows=[dict(instance=inst,function_id=61,statement=29599,lemma=lemmas[0],all_caller_lemmas=lemmas)]
 x=dict(rows=rows,count=1,chunks=[name],all_scalar_callers=obs,endpoint_rows=values,initializer_events=events,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 all actual scalar/table row callers and exact shift projection plus named kernel guards',validation_status='PREPARATION; compile and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,t in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'ROW-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=1,caller_cases=19,check=a.check,controls=controls)))
if __name__=='__main__':main()
