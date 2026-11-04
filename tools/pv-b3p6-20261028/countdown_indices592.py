"""Bind literal/actual array-metadata initial counters and complete private
positive-test/decrement loop frames. No arbitrary bound premise is introduced.
"""
from pathlib import Path
import json,lzma,hashlib,argparse,copy
from source_normalize583 import normalize
from initializer_source578 import compact,find,nodes
from frame_indices578 import root,dicts
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
SPECS=[(7,91,1261,1267,1269,29218,24,24),(7,91,1359,1365,1367,29223,4,4),(234,4,18134,18139,18141,30396,9,16)]
def certify(fs,t):
 for fid in[7,234]:assert compact(fs[fid]['body'])==t[str(fid)]
 rows=[];frames=[]
 for fid,slot,init,test,dec,site,start,length in SPECS:
  b,changes=normalize(fs[fid]['body'],{})
  k=find(b,init)['kind']['Assign'];assert root(k[0])==slot
  if fid==7 and init==1359:
   assert compact(k[1])=={'Use':[{'Move':{'kind':{'Local':102}}},'Yes']};k=find(b,1357)['kind']['Assign']
  assert k[1]['Use'][0]['Const']and literal(k[1]['Use'][0]['Const'])==start
  predicate=compact(find(b,test)['kind']['Assign'][1]);assert predicate['BinaryOp'][0]=='Gt'and literal(predicate['BinaryOp'][2]['Const'])==0
  decrement=compact(find(b,dec)['kind']['Assign']);assert decrement==[{'kind':{'Local':slot}},{'BinaryOp':[{'Sub':'Wrap'},{'Copy':{'kind':{'Local':slot}}},{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','1']}}}}}]}]
  # The smallest loop containing the decrement is the countdown loop.
  loops=[q for q in nodes(b)if isinstance(q['kind'],dict)and'Loop'in q['kind']and find(q['kind']['Loop'],dec)]
  loop=min(loops,key=lambda q:len(list(nodes(q['kind']['Loop']))))['kind']['Loop']
  writes=[q['id']for q in nodes(loop)if isinstance(q['kind'],dict)and'Assign'in q['kind']and root(q['kind']['Assign'][0])==slot]
  assert writes==[dec]
  for x in dicts(loop):
   for tag in ['Ref','RawPtr']:
    if tag in x:assert root(x[tag].get('place',{}))!=slot
   if'Move'in x:assert root(x['Move'])!=slot
   if x.get('kind')in['StorageLive','StorageDead']:raise AssertionError('unexpected form')
  c=find(b,site)['kind']['Call']['call'];assert literal(c['func']['Regular']['generics']['const_generics'][0])==length
  frames.append(dict(function_id=fid,slot=slot,initial_statement=init,initial=start,test=test,decrement=dec,site=site,sole_loop_write=writes,metadata_normalizations=changes))
  rows.append(dict(function_id=fid,statement=site,initial=start,length=length,slack=length-start))
 return rows,frames

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'COUNTDOWN-TEMPLATE-D592.json').read_text());rows,frames=certify(fs,t);controls={}
 for fid,sid,label in[(7,1269,'changed_decrement'),(7,1357,'changed_metadata'),(234,18139,'changed_positive_test')]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_CountdownIndices592227';s='import PV_B3P_CountdownEvents592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r.update(instance=next(k for k,v in g['instances'].items()if v['id']==r['function_id']),lemma=name+f'.certificate_{j}');args=f'{r["initial"]}#usize {r["slack"]} n effects'
  s+=f'''/-- Checked source counter frame at {r['instance']}:{r['statement']}. -/
theorem certificate_{j} {{α : Type}} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_CountdownEvents592227.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_CountdownEvents592227.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 x=dict(rows=rows,count=3,chunks=[name],frames=frames,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 literal/array-metadata countdown frames plus kernel counter invariant and guards',validation_status='PREPARATION; compile and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,t in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'COUNTDOWN-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=3,check=a.check,controls=controls)))
if __name__=='__main__':main()
