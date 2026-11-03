"""Actual constructor/caller/private-field mapping for IndexRange207/329.

The captured source chain is18 ->44(array into_iter) ->45(fold) ->207
(IndexRange try_fold) ->329(element-reading callback). Six local numeric
checks are consumed. Pointer transmutation/read/drop semantics remain open.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from initializer_source578 import compact,find,nodes
from frame_indices578 import root
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def prefix18(f):
 b=f['body']['Structured']['body']['statements'];cut=next(i for i,s in enumerate(b)if s['id']==2376);return b[:cut+1]
def certify(fs,t):
 assert compact(prefix18(fs[18]))==t['18_prefix']
 for n in [44,45,207,329]:assert compact(fs[n]['body'])==t[str(n)]
 array=find(fs[18]['body'],2360)['kind']['Assign'][1]['Aggregate'];assert array[0]['Array'][1]['kind']['Literal']['Scalar']['Unsigned']==['Usize','3']and len(array[1])==3
 assert [a['Const']['kind']['Literal']['Scalar']['Unsigned']for a in array[1]]==[['Usize','1'],['Usize','9'],['Usize','10']]
 for sid,fid,args in [(2365,44,[7]),(2376,45,[6,None,8]),(4079,207,[9,2,10])]:
  f=18 if sid<4000 else 45;c=find(fs[f]['body'],sid)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':fid}and len(c['args'])==len(args)
  for op,slot in zip(c['args'],args):
   if slot is not None:assert op['Move']['kind']=={'Local':slot}
 cursor=find(fs[44]['body'],4039)['kind']['Assign'][1]['Aggregate'];assert cursor[0]['Adt'][0]['id']=={'Adt':68}
 assert cursor[1][0]['Const']['kind']['Literal']['Scalar']['Unsigned']==['Usize','0']and cursor[1][1]['Const']['kind']['Var']=={'Free':0}
 unsize=find(fs[45]['body'],4057)['kind']['Assign'][1]['UnaryOp'][0]['Cast']['Unsize'];assert compact(unsize[-1])=={'Length':{'kind':{'Var':{'Free':0}}}}
 # Split inner.alive and inner.data: source closure never receives &mut alive.
 data=find(fs[45]['body'],4063)['kind']['Assign'][1]['Ref']['place']['kind']['Projection'];alive=find(fs[45]['body'],4065)['kind']['Assign'][1]['Ref']['place']['kind']['Projection']
 assert data[0]==alive[0]and data[1]=={'Field':[{'Adt':[67,None]},1]}and alive[1]=={'Field':[{'Adt':[67,None]},0]}
 closure=find(fs[45]['body'],4067)['kind']['Assign'][1]['Aggregate'];assert closure[0]['Adt'][0]['id']=={'Adt':73}and closure[1][0]['Copy']['kind']=={'Local':8}
 # The only source write through self is start := old_start+1. End is framed.
 writes=[];refs=[]
 for st in nodes(fs[207]['body']):
  k=st['kind']
  if not isinstance(k,dict)or 'Assign'not in k:continue
  dest,rhs=k['Assign']
  if root(dest)==1:writes.append(st['id'])
  for tag in ['Ref','RawPtr']:
   if tag in rhs and root(rhs[tag]['place'])==1:refs.append(st['id'])
 assert writes==[9887]and refs==[]
 dest,rhs=find(fs[207]['body'],9887)['kind']['Assign'];assert dest['kind']['Projection'][1]=={'Field':[{'Adt':[68,None]},0]}
 add=find(fs[207]['body'],9886)['kind']['Assign'][1]['BinaryOp'];assert add[0]=={'Add':'UB'}and add[1]['Copy']['kind']=={'Local':7}and add[2]['Const']['kind']['Literal']['Scalar']['Unsigned']==['Usize','1']
 loop=find(fs[207]['body'],10085)['kind']['Loop'];condition=find(loop,9863)['kind']['Assign'][1]['BinaryOp'];assert condition[0]=='Ne'
 # old_start remains local7 after the private increment and is passed by
 # scalar copy to the user callback. No reference to self is handed out.
 tuplearg=find(loop,9897)['kind']['Assign'][1]['Aggregate'][1];assert tuplearg[1]['Copy']['kind']=={'Local':7}
 # Callback input tuple's index and separately borrowed data metadata supply
 # every local check. These checks all precede native pointer reads.
 assert find(fs[329]['body'],23381)['kind']['Assign'][1]['Use'][0]['Move']['kind']['Projection'][1]=={'Field':[{'Tuple':2},1]}
 bound=find(fs[329]['body'],23406)['kind']['Assign'][1]['BinaryOp'];assert bound[0]=='Lt'and bound[1]['Copy']['kind']=={'Local':4}
 return dict(constructor=4039,constructor_length=3,caller_array=2360,caller_into_iter=2365,caller_fold=2376,fold_unsize_metadata=4057,fold_data_borrow=4063,fold_cursor_borrow=4065,fold_callback_capture=4067,fold_call=4079,loop_test=9863,only_cursor_write=9887,cursor_increment=9886,callback_old_index=9897,callback_source_index=23381,callback_source_comparison=23406,private_cursor_address_does_not_escape=True,data_cursor_source_fields_disjoint=True)
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};t=json.loads((R/'INDEX-CURSOR-TEMPLATE-D579.json').read_text());binding=certify(fs,t)
 g=json.loads((I/'direct3-instantiated-callcone.json').read_text());instances={}
 for fid in [18,44,45,207,329]:
  matches=[(k,v)for k,v in g['instances'].items()if v['id']==fid];assert len(matches)==1;instances[fid]=dict(instance=matches[0][0],**matches[0][1])
 for fid in [44,45]:assert instances[fid]['environment']['types'][0]=={'Literal':{'UInt':'Usize'}}and instances[fid]['environment']['const_generics'][0]['kind']['Literal']['Scalar']['Unsigned']==['Usize','3']
 assert instances[329]['environment']['types'][0]=={'Literal':{'UInt':'Usize'}}
 for callee,caller in [(44,18),(45,18),(207,45),(329,207)]:
  incoming=[e for e in g['edges']if e['callee_id']==callee];assert len(incoming)==1 and incoming[0]['caller']==instances[caller]['instance']
 # Deployed/extractor complete source-body parity was already checked.
 parity=json.loads((R/'ARRAY-CURSOR-SOURCE-D571.json').read_text());assert all(x['body_tokens_identical']for x in parity['items'])
 controlparity=json.loads((R/'CONTROL-SOURCE-PARITY-D569.json').read_text());assert all(x['body_tokens_identical']for x in controlparity['body_comparisons']if x['path']=='ops/index_range.rs')
 controls={}
 def edit44(f):find(f[44]['body'],4039)['kind']['Assign'][1]['Aggregate'][1][0]['Const']['kind']['Literal']['Scalar']['Unsigned'][1]='1'
 edits={
  'nonzero_initial_cursor':edit44,
  'caller_size_change':lambda f:find(f[18]['body'],2360)['kind']['Assign'][1]['Aggregate'][0]['Array'][1]['kind']['Literal']['Scalar']['Unsigned'].__setitem__(1,'4'),
  'overlap_cursor_and_data':lambda f:find(f[45]['body'],4063)['kind']['Assign'][1]['Ref']['place']['kind']['Projection'][1]['Field'].__setitem__(1,0),
  'closure_captures_cursor':lambda f:find(f[45]['body'],4067)['kind']['Assign'][1]['Aggregate'][1][0]['Copy']['kind'].__setitem__('Local',9),
  'write_end_instead_of_start':lambda f:find(f[207]['body'],9887)['kind']['Assign'][0]['kind']['Projection'][1]['Field'].__setitem__(1,1),
  'wrong_increment':lambda f:find(f[207]['body'],9886)['kind']['Assign'][1]['BinaryOp'][2]['Const']['kind']['Literal']['Scalar']['Unsigned'].__setitem__(1,'2'),
  'wrong_callback_index':lambda f:find(f[207]['body'],9897)['kind']['Assign'][1]['Aggregate'][1][1]['Copy']['kind'].__setitem__('Local',21),
 }
 for name,edit in edits.items():
  changed=copy.deepcopy(fs);edit(changed)
  try:certify(changed,t)
  except(AssertionError,KeyError):controls[name]='rejected'
  else:raise AssertionError(name)
 descriptors=[(207,9851,'ordered'),(207,9856,'ordered'),(207,9882,'add'),(329,23398,'index'),(329,30694,'index'),(329,23409,'callbackAssertion')];rows=[]
 s='import PV_B3P_IndexCounter579227\nnamespace PV_B3P_IndexCursorFamily579227\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_IndexCounter579227\nset_option autoImplicit false\n'
 for fid,sid,kind in descriptors:
  name=f'certificate_{fid}_{sid}';rows.append(dict(instance=instances[fid]['instance'],statement=sid,kind=kind,lemma='PV_B3P_IndexCursorFamily579227.'+name))
  s+=f'/-- Actual constructor/caller chain18/44/45/207/329, instruction{sid}. -/\n'
  if kind=='ordered':
   s+=f'''theorem {name} {{α : Type}} (normal first second : Result α) :
    ¬ diagnostic (orderedCondition 0 3#usize = true) ∧
      branch (orderedCondition 0 3#usize = true) normal first = branch (orderedCondition 0 3#usize = true) normal second :=
  ordered_certificate 0 3#usize normal first second
'''
  elif kind=='add':
   s+=f'''theorem {name} {{α : Type}} (n : Nat) (checks : Bool) (observed : ArithmeticState)
    (ran : addEvent n 3#usize checks = some observed) (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  add_certificate n 3#usize checks observed ran normal first second
'''
  else:
   guard='indexGuard observed'if kind=='index'else'decide (indexGuard observed) = true';lemma='index_certificate'if kind=='index'else'callback_assertion_certificate'
   s+=f'''theorem {name} {{α : Type}} (n : Nat) (observed : IndexState)
    (ran : indexEvent n 3#usize = some observed) (normal first second : Result α) :
    ¬ diagnostic ({guard}) ∧
      branch ({guard}) normal first = branch ({guard}) normal second :=
  {lemma} n 3#usize observed ran normal first second
'''
  s+=f'#print axioms {name}\n'
 s+='end PV_B3P_IndexCursorFamily579227\n'
 meta=dict(llbc_sha256=sha(raw),rows=rows,count=len(rows),template_sha256=sha((R/'INDEX-CURSOR-TEMPLATE-D579.json').read_bytes()),binding=binding,instances=instances,negative_controls=controls,source_parity_reused=['ARRAY-CURSOR-SOURCE-D571.json','CONTROL-SOURCE-PARITY-D569.json / ops/index_range.rs'],evidence_class='script-checked own-1 actual array constructor/caller/private cursor/data metadata mapping plus Lean generated scalar event guards',native_pointer_validity=False,transmute_layout=False,array_element_restoration=False,partial_initialization_and_drop=False,whole_caller_association=False,premises_removed=[])
 for out,text in {D/'lean/PV_B3P_IndexCursorFamily579227.lean':s,R/'INDEX-CURSOR-SOURCE-D579.json':json.dumps(meta,indent=2)+'\n'}.items():
  if a.check:assert out.read_text()==text,out
  else:out.write_text(text)
 print(json.dumps(dict(local_checks=len(rows),source_chain=[18,44,45,207,329],controls=controls,check=a.check)))
if __name__=='__main__':main()
