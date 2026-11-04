"""Scalar immutable captures across two actual array initializer layers.
Native pointer and full borrow restoration remain separate obligations.
"""
from pathlib import Path
import json,lzma,hashlib,copy,argparse
from initializer_source578 import compact,find,nodes
from frame_indices578 import root,dicts
from callback_indices584 import source_chain
from capture_collect587 import collect as captures
from capture_arithmetic587 import collect as arithmetic
from computed_indices583 import render
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def chain(g,fid,caller):
 cur=next(k for k,v in g['instances'].items()if v['id']==fid);out=[]
 for expected in[364,370,229,53,caller]:
  ins=[e for e in g['edges']if e['callee']==cur];assert len(ins)==1;cur=ins[0]['caller'];assert g['instances'][cur]['id']==expected;out.append(ins[0])
  if expected==229:assert literal(g['instances'][cur]['environment']['const_generics'][0])==4
 return out

def certify(fs,g,t):
 for fid in[53,218,428,430,524,529,536]:assert compact(fs[fid]['body'])==t[str(fid)]
 source_chain(fs,json.loads((R/'CALLBACK-TEMPLATE-D584.json').read_text()))
 chains=[chain(g,428,218),chain(g,524,430),chain(g,536,529),chain(g,430,218),chain(g,529,494)]
 # Source53 wraps f by value, then forwards that exact wrapper into source229.
 c=find(fs[53]['body'],4683)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':229}and compact(c['args'])==[{'Move':{'kind':{'Local':3}}}]
 frames=[]
 obs=next(r for r in captures(fs[218]['body'],scalar_slots=[21])if r['statement']==11907);mark=obs['arguments'][0][2][1];assert mark[0]=='scalarRef';value=mark[1];assert next(v for k,v in obs['bounds']if k==value)[0]==4
 frames.append(dict(caller=218,capture=obs,leaf=428))
 for fid,leaf,extract,ref,aggregate,call in[(430,524,26255,26261,26262,26270),(529,536,28726,28732,28733,28741)]:
  b=copy.deepcopy(fs[fid]['body']);k=find(b,extract)['kind']['Assign'];assert k[0]['kind']=={'Local':3}and compact(k[1]['Use'][0])=={'Move':{'kind':{'Projection':[{'kind':{'Local':2}},{'Field':[{'Tuple':1},0]}]}}}
  # The fresh scalar can only be read or immutably borrowed. No reference to
  # its stack slot can give the nested callbacks mutation capability.
  writes=[];borrows=[]
  for st in nodes(b):
   kk=st['kind']
   if not isinstance(kk,dict):continue
   if 'Assign'in kk:
    dest,rhs=kk['Assign']
    if root(dest)==3:writes.append(st['id'])
    for tag in ['Ref','RawPtr']:
     if tag in rhs and root(rhs[tag]['place'])==3:
      assert tag=='Ref'and rhs[tag]['kind']=='Shared';borrows.append(st['id'])
   if 'Drop'in kk:assert root(kk['Drop']['place'])!=3
  assert writes==[extract]and borrows==[ref]
  k[1]['Use'][0]={'Copy':{'kind':{'Local':777}}};v=('snapshot','outer_initializer',fid);obs=next(r for r in captures(b,initial=({777:v},{v:(4,24724,24985)}),scalar_slots=[3])if r['statement']==call)
  assert obs['arguments'][0][2][1]==('scalarRef',v);assert next(val for key,val in obs['bounds']if key==v)[0]==4
  frames.append(dict(caller=fid,leaf=leaf,tuple_extract=extract,shared_capture=ref,only_scalar_write=writes,capture=obs))
 # Both panic matches read field1, the immutable scalar reference just bound.
 for fid,adt,read,switch,panic in[(428,92,26015,26181,26180),(536,124,28953,29119,29118)]:
  assert compact(find(fs[fid]['body'],read)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Projection':[{'kind':{'Projection':[{'kind':{'Local':1}},'Deref']}},{'Field':[{'Adt':[adt,None]},1]}]}}}
  x=find(fs[fid]['body'],switch)['kind']['Switch']['SwitchInt'];assert compact(x[0])=={'Copy':{'kind':{'Projection':[{'kind':{'Local':57}},'Deref']}}};assert [literal({'kind':{'Literal':v[0][0]}})for v in x[2]]==[0,1,2,3];assert any(q['id']==panic for q in x[3]['statements'])
 b=copy.deepcopy(fs[524]['body']);aliases=set();rewrites=[]
 for st in b['Structured']['body']['statements']:
  k=st['kind']
  if not isinstance(k,dict)or'Assign'not in k:continue
  dest,rhs=k['Assign'];op=rhs.get('Use',[None])[0]
  if not isinstance(op,dict):continue
  kind=compact(op).get('Copy',{}).get('kind',{})
  if kind=={'Projection':[{'kind':{'Projection':[{'kind':{'Local':1}},'Deref']}},{'Field':[{'Adt':[118,None]},1]}]}:aliases.add(root(dest))
  elif any(kind=={'Projection':[{'kind':{'Local':slot}},'Deref']}for slot in aliases):
   rewrites.append(dict(statement=st['id'],source=copy.deepcopy(st)));rhs['Use'][0]={'Copy':{'kind':{'Local':777}}}
 assert len(rewrites)==4
 mark=('snapshot','captured_column',524);expr=dict(op='bounded',input=mark,limit=4);rs=arithmetic(b,initial=({777:mark},{mark:(4,24724,24985),('expr',mark):expr}));rs=[r for r in rs if r['statement']in[31238,31248,31258,31268]];assert len(rs)==4
 return rs,dict(source_chains=chains,frames=frames,leaf_scalar_read_projections=rewrites)
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'CAPTURE-TEMPLATE-D587.json').read_text());rows,binding=certify(fs,g,t);controls={}
 for fid,sid,label in[(218,11886,'changed_caller_test'),(430,26261,'changed_scalar_capture'),(529,28726,'changed_outer_index'),(524,28405,'changed_captured_read'),(536,29119,'changed_match')]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_CaptureGuards587227';s='import PV_B3P_ArithmeticEvents583227\nimport PV_B3P_FourWayEvents587227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n';allrows=[]
 for j,r in enumerate(rows):
  inputs=[];expr=render(r['expression'],inputs);assert len(inputs)==1;inst=next(k for k,v in g['instances'].items()if v['id']==524);r.update(instance=inst,function_id=524,lemma=name+f'.certificate_{j}');allrows.append(r);args=f'{expr} {r["slack"]} effects'
  s+=f'''/-- Captured source outer column at {inst}:{r['statement']}. -/
def sourceState_{j} (input0 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent {args}
theorem certificate_{j} {{α : Type}} (input0 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} input0 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 for fid,sid in[(428,26180),(536,29118)]:
  label=f'panic_{fid}';inst=next(k for k,v in g['instances'].items()if v['id']==fid);allrows.append(dict(instance=inst,function_id=fid,statement=sid,lemma=name+'.'+label))
  s+=f'''/-- Actual four-arm source match at {inst}:{sid}. -/
def sourceState_{label} (column : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent 4 0 column effects
theorem {label} {{α : Type}} (column : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{label} column effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (PV_B3P_FourWayEvents587227.sourceCondition observed = true) ∧
      branch (PV_B3P_FourWayEvents587227.sourceCondition observed = true) normal first =
        branch (PV_B3P_FourWayEvents587227.sourceCondition observed = true) normal second :=
  PV_B3P_FourWayEvents587227.event_certificate column effects observed ran normal first second
#print axioms {label}
'''
 x=dict(rows=allrows,count=6,chunks=[name],binding=binding,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 immutable scalar capture/caller-test projection plus named kernel guards',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,native_borrow_restoration=False,premises_removed=[])
 for p,s in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'CAPTURE-GUARDS-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=4,new_panics=2,check=a.check,controls=controls)))
if __name__=='__main__':main()
