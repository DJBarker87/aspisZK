"""Bind both slice-next ZST subtraction observations; preserve pointer gap."""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from initializer_source578 import compact,find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def certify(f,template,switch,event):
 assert compact(f['body'])==template
 cond,ty,arms,default=find(f['body'],switch)['kind']['Switch']['SwitchInt']
 assert cond['Copy']['kind']=={'Local':4} and ty=={'UInt':'Usize'}
 assert len(arms)==1 and arms[0][0]==[{'Scalar':{'Unsigned':['Usize','0']}}] and not arms[0][1]['statements']
 call=find(default,event)['kind']['Call']['call'];assert call['func']['Regular']['kind']['Fun']=={'Regular':317}
 assert call['args'][0]['Copy']['kind']=={'Local':4}
 assert call['args'][1]['Const']['kind']['Literal']['Scalar']['Unsigned']==['Usize','1']
 # No private encodedEnd write or effect precedes this event in the default
 # prefix: only StorageLive, UbChecks and the matching If are permitted.
 prefix=default['statements'];gate=next(i for i,s in enumerate(prefix)if isinstance(s['kind'],dict)and 'Switch'in s['kind']);pre=prefix[:gate]
 assert all('StorageLive'in s['kind'] or ('Assign'in s['kind']and s['kind']['Assign'][1].get('NullaryOp',[None])[0]=='UbChecks')for s in pre)
 test,yes,no=prefix[gate]['kind']['Switch']['If'];assert not no['statements'] and len(yes['statements'])==1 and yes['statements'][0]['id']==event
 return dict(source_switch=switch,nonzero_scalar_local=4,source_event=event,precondition_call=call,full_body_sha256=sha(json.dumps(f['body'],sort_keys=True).encode()))
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());template=json.loads((R/'SLICE-TEMPLATE-D578.json').read_text());rows=[];controls={}
 parity=json.loads((R/'CONTROL-SOURCE-PARITY-D569.json').read_text());assert next(v for v in parity['body_comparisons']if v['item']=='fn next(')['body_tokens_identical']
 for fid,switch,event in [(192,9398,9376),(237,18346,18322)]:
  source=certify(fs[fid],template[str(fid)],switch,event)
  for label,edit in {
   'wrong_empty_case':lambda x:find(x['body'],switch)['kind']['Switch']['SwitchInt'][2][0][0][0]['Scalar']['Unsigned'].__setitem__(1,'1'),
   'wrong_operand':lambda x:find(x['body'],event)['kind']['Call']['call']['args'][0]['Copy']['kind'].__setitem__('Local',2),
   'wrong_decrement':lambda x:find(x['body'],event)['kind']['Call']['call']['args'][1]['Const']['kind']['Literal']['Scalar']['Unsigned'].__setitem__(1,'2'),
  }.items():
   changed=copy.deepcopy(fs[fid]);edit(changed)
   try:certify(changed,template[str(fid)],switch,event)
   except(AssertionError,KeyError):controls[f'{fid}:{label}']='rejected'
   else:raise AssertionError(label)
  for inst,v in g['instances'].items():
   if v['id']==fid:rows.append(dict(instance=inst,environment=v['environment'],statement=event,lemma=f'PV_B3P_SliceFamily578227.certificate_{fid}',**source))
 assert len(rows)==2
 s='import PV_B3P_SliceEvents578227\nnamespace PV_B3P_SliceFamily578227\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_SliceEvents578227\nset_option autoImplicit false\n'
 for fid in [192,237]:
  s+=f'''def sourceState_{fid} (zeroSized checks : Bool) (encodedEnd : Usize) : Option ArithmeticState :=
  sourceEvent zeroSized checks encodedEnd
theorem certificate_{fid} {{α : Type}} (zeroSized checks : Bool) (encodedEnd : Usize)
    (observed : ArithmeticState) (ran : sourceState_{fid} zeroSized checks encodedEnd = some observed)
    (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  event_certificate zeroSized checks encodedEnd observed ran normal first second
#print axioms certificate_{fid}
'''
 s+='end PV_B3P_SliceFamily578227\n'
 meta=dict(rows=rows,count=len(rows),negative_controls=controls,llbc_sha256=sha(raw),template_sha256=sha((R/'SLICE-TEMPLATE-D578.json').read_bytes()),source_parity_reused='CONTROL-SOURCE-PARITY-D569.json / fn next(',evidence_class='script-checked own-1 exact ZST source-event projection with Lean subtraction guard',native_pointer_validity=False,non_ZST_pointer_offset=False,borrow_restoration=False,whole_caller_association=False,premises_removed=[])
 for p,t in {D/'lean/PV_B3P_SliceFamily578227.lean':s,R/'SLICE-SOURCE-D578.json':json.dumps(meta,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(source_certificates=len(rows),negative_controls=controls,check=a.check)))
if __name__=='__main__':main()
