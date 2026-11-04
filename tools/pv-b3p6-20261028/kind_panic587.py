"""Mechanically project all136 COPY_LINKS literal initializer entries.
No large literal is kernel-reduced; each projected kind uses a named Fin5 cell.
"""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from initializer_source578 import compact,find
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def unsigned(v):
 x=v.get('kind',{}).get('Literal',{}).get('Scalar',{}).get('Unsigned');assert x and x[0]in['U8','U16','U32','U64','Usize'];return int(x[1])
def initialize(f):
 b=f['body']['Structured'];assert b['locals']['arg_count']==0;env={};events=[];returned=False
 def operand(o):
  if 'Const'in o:
   return unsigned(o['Const'])
  tag,p=next(iter(o.items()));assert tag in['Copy','Move']and'Local'in p['kind'];slot=p['kind']['Local'];value=env[slot]
  if tag=='Move':del env[slot]
  return copy.deepcopy(value)
 for st in b['body']['statements']:
  assert not returned
  k=st['kind']
  if k=='Return':returned=True;continue
  assert isinstance(k,dict)
  if 'StorageLive'in k or'StorageDead'in k:continue
  assert list(k)==['Assign'];dest,rhs=k['Assign'];assert 'Local'in dest['kind'];slot=dest['kind']['Local']
  if 'Use'in rhs:assert list(rhs)==['Use'];value=operand(rhs['Use'][0])
  else:
   assert list(rhs)==['Aggregate'];tag,fields=rhs['Aggregate'];values=[operand(o)for o in fields];value=dict(tag=compact(tag),fields=values)
  env[slot]=value;events.append(dict(statement=st['id'],destination=slot))
 assert returned and set(env)=={0};value=env[0];assert value['tag'].get('Array')is not None and literal(value['tag']['Array'][1])==136 and len(value['fields'])==136
 kinds=[]
 for row in value['fields']:
  assert row['tag']['Adt'][0]['id']=={'Adt':33}and len(row['fields'])==5
  kind=row['fields'][1];assert isinstance(kind,int)and 0<=kind<5;kinds.append(kind)
 return kinds,events

def certify(ll,fs,g,t):
 for fid in[21,68,250]:assert compact(fs[fid]['body'])==t[str(fid)]
 gl=next(x for x in ll['global_decls']if x and x['def_id']==11);assert gl['global_kind']=='NamedConst'and compact(gl['value'])=={'kind':{'Call':[{'kind':{'Fun':{'Regular':247}}},[]]}}
 kinds,events=initialize(fs[247]);c=find(fs[21]['body'],2977)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':68}and compact(c['args'][0])=={'Move':{'kind':{'Local':23}}}
 assert compact(find(fs[21]['body'],2952)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Global':{'id':11}}}}
 assert compact(find(fs[21]['body'],2957)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Projection':[{'kind':{'Local':58}},'Deref']}}}
 assert compact(find(fs[21]['body'],2962)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Local':19}}}
 x=find(fs[68]['body'],7707)['kind']['Switch']['SwitchInt'];assert compact(x[0])=={'Copy':{'kind':{'Projection':[{'kind':{'Local':1}},{'Field':[{'Adt':[33,None]},1]}]}}}and [unsigned({'kind':{'Literal':q[0][0]}})for q in x[2]]==list(range(5))
 assert {7698,7706}<={s['id']for s in x[3]['statements']}
 for callee,caller in[(68,21),(250,68)]:
  ins=[e for e in g['edges']if e['callee_id']==callee];assert len(ins)==1 and ins[0]['caller'].startswith(str(caller)+':')
 return kinds,dict(global_id=11,initializer=247,initializer_sha256=sha(json.dumps(fs[247]['body'],sort_keys=True).encode()),complete_initializer_events=events,entry_count=136,index_call=29285,element_snapshot=2957,link_argument_copy=2962,link_call=2977,kind_switch=7707,default_sites=[7698,7706],only_forward_caller='250 <-68 <-21',native_global_initialization=False)
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'KIND-PANIC-TEMPLATE-D587.json').read_text());kinds,binding=certify(ll,fs,g,t);controls={}
 changed=copy.deepcopy(fs);first=next(st for st in changed[247]['body']['Structured']['body']['statements']if isinstance(st['kind'],dict)and'Assign'in st['kind']and st['kind']['Assign'][1].get('Aggregate',[{}])[0].get('Adt',[{}])[0].get('id')=={'Adt':33});first['kind']['Assign'][1]['Aggregate'][1][1]['Const']['kind']['Literal']['Scalar']['Unsigned'][1]='5'
 try:certify(ll,changed,g,t)
 except(AssertionError,KeyError):controls['out_of_domain_literal_kind']='rejected'
 else:raise AssertionError('invalid kind accepted')
 for fid,sid,label in[(21,2962,'changed_link_snapshot'),(68,7707,'changed_kind_switch')]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:certify(ll,changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_KindPanic587227';s='import PV_B3P_KindEvents587227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_KindEvents587227\nset_option autoImplicit false\n/-- Source247 complete literal initializer, weight_kind projection only. -/\ndef sourceKinds : List (Fin 5) := [\n  '+',\n  '.join('kind'+str(k)for k in kinds)+']\n';rows=[]
 for fid,sid in[(68,7698),(68,7706),(250,21441)]:
  inst=next(k for k,v in g['instances'].items()if v['id']==fid);label=f'certificate_{fid}_{sid}';rows.append(dict(instance=inst,function_id=fid,statement=sid,lemma=name+'.'+label))
  s+=f'''/-- Actual COPY_LINKS incoming/default exclusion at {inst}:{sid}. -/
theorem {label} {{α : Type}} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent sourceKinds index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (sourceCondition observed = true) ∧
      branch (sourceCondition observed = true) normal first = branch (sourceCondition observed = true) normal second :=
  event_certificate sourceKinds index effects observed ran normal first second
#print axioms {label}
'''
 x=dict(rows=rows,count=3,chunks=[name],binding=binding,kinds=kinds,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 complete immutable literal initializer kind projection and actual incoming/default map plus named kernel guards',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',native_global_initialization=False,whole_caller_association=False,premises_removed=[])
 for p,s in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'KIND-PANIC-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_panics=3,table_entries=136,check=a.check,controls=controls)))
if __name__=='__main__':main()
