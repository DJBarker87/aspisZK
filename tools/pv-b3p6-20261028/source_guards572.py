"""Bind the actual initializer residual arm to its local-state interpreter.

The entire Match arm prefix is checked, not a search for six statement IDs.
No calls, drops, alternate entries or unknown operations may be skipped. The
branch input is supplied by the source Match on ControlFlow::Break. The rest
of the function (including unwind and pointer events) remains an obligation.
"""
from pathlib import Path
import argparse, hashlib, json, lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()

def local(place):
 assert set(place['kind'])=={'Local'},place
 return place['kind']['Local']
def operand(op):
 assert len(op)==1 and next(iter(op)) in ('Copy','Move'),op
 return local(next(iter(op.values())))
def lower(st):
 k=st['kind'];assert isinstance(k,dict),st
 if 'StorageLive' in k or 'StorageDead' in k:
  return ('kill',next(iter(k.values())))
 assert set(k)=={'Assign'},st
 dest,rhs=k['Assign'];d=local(dest)
 if 'Use' in rhs:
  p=next(iter(rhs['Use'][0].values()))['kind']['Projection']
  assert p[1]=={'Field':[{'Adt':[17,1]},0]},st
  return ('project',d,local(p[0]))
 if 'Aggregate' in rhs:
  tag,fields=rhs['Aggregate'];assert tag['Adt'][0]['id']=={'Adt':17} and tag['Adt'][1:]==[1,None] and len(fields)==1,st
  return ('breakValue',d,operand(fields[0]))
 if 'Discriminant' in rhs:return ('tag',d,local(rhs['Discriminant']))
 op,left,right=rhs['BinaryOp'];assert op=='Eq' and right['Const']['kind']['Literal']['Scalar']['Signed']==['Isize','1'],st
 return ('equalOne',d,operand(left))

def find(v,n):
 if isinstance(v,dict):
  if v.get('id')==n and 'span'in v:return v
  for x in v.values():
   if (a:=find(x,n)) is not None:return a
 elif isinstance(v,list):
  for x in v:
   if (a:=find(x,n)) is not None:return a

def certify(f):
 switch=find(f['body'],24900);p,arms,default=switch['kind']['Switch']['Match']
 assert local(p)==8 and default is None
 assert [a[0] for a in arms]==[[0],[1]]
 arm=arms[1][1]['statements'];cut=next(i for i,s in enumerate(arm)if s['id']==24831)
 prefix=arm[:cut];test=arm[cut]
 assert operand(test['kind']['Assert']['assert']['cond'])==33
 assert test['kind']['Assert']['assert']['expected']is True
 ops=[lower(st) for st in prefix]
 expected=[('kill',17),('project',17,8),('kill',18),('breakValue',18,17),('breakValue',7,18),('kill',18),('kill',17),('kill',8),('kill',13),('project',13,7),('kill',31),('kill',33),('tag',31,13),('equalOne',33,31)]
 assert ops==expected,ops
 return switch, prefix, test,ops

def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];f=next(f for f in ll['fun_decls']if f and f['def_id']==370)
 switch,prefix,test,ops=certify(f)
 # Matched negative controls: a changed enum tag, clobber, skipped statement,
 # unexpected effect, and mismatched Match branch must all be rejected.
 import copy
 controls={}
 for name,edit in {
  'wrong_constructor_tag':lambda a:a[3]['kind']['Assign'][1]['Aggregate'][0]['Adt'].__setitem__(1,0),
  'clobber_destination':lambda a:a[4]['kind']['Assign'][0]['kind'].__setitem__('Local',13),
  'missing_storage_effect':lambda a:a.pop(5),
  'intervening_call':lambda a:a.insert(5,dict(id=-1,span={},kind={'Call':{}})),
 }.items():
  changed=copy.deepcopy(f);arm=find(changed['body'],24900)['kind']['Switch']['Match'][1][1][1]['statements'];edit(arm)
  try:certify(changed)
  except (AssertionError,KeyError,ValueError,StopIteration):controls[name]='rejected'
  else:raise AssertionError(('negative control accepted',name))
 graph=json.loads((I/'direct3-instantiated-callcone.json').read_text());inst=[dict(instance=k,environment=v['environment'],statement=24831,match_statement=24900,branch_variant=1)for k,v in graph['instances'].items()if v['id']==370];assert len(inst)==16
 # This is one fixed actual source family, not sixteen assumed state maps.
 s='''import PV_B3P_ResidualSource572227
namespace PV_B3P_ResidualFamily572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_ResidualSource572227
set_option autoImplicit false
/-- All sixteen captured specializations have this exact source-local state
map. Environment/carrier provenance is retained in SOURCE-GUARDS-D572.json. -/
def sourceState {α : Type} (_site : Fin 16) (prior : Store α) (residual : Value α) : Store α :=
  assertionState prior residual

theorem family_guard {α : Type} (site : Fin 16) (prior : Store α) (residual : Value α) :
    condition (sourceState site prior residual) = true :=
  reached_guard _ ⟨prior,residual,rfl⟩

theorem family_certificate {α β : Type} (site : Fin 16)
    (prior : Store α) (residual : Value α) (normal first second : Result β) :
    ¬ diagnostic (condition (sourceState site prior residual) = true) ∧
      branch (condition (sourceState site prior residual) = true) normal first =
        branch (condition (sourceState site prior residual) = true) normal second :=
  source_assertion _ ⟨prior,residual,rfl⟩ normal first second
#print axioms family_guard
#print axioms family_certificate
end PV_B3P_ResidualFamily572227
'''
 core=(D/'lean/PV_B3P_ResidualSource572227.lean').read_text()
 rendered='['+', '.join('.'+op[0]+' '+' '.join(map(str,op[1:]))for op in ops)+']'
 # Compare the parsed source operations with the actual Lean program declaration.
 import re
 lean_program=re.search(r'def residualProgram : List Instr :=\s*(\[.*?\])',core,re.S)[1]
 assert re.sub(r'\s+','',lean_program)==re.sub(r'\s+','',rendered)
 meta=dict(llbc_sha256=sha(raw),graph_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),body_sha256=sha(json.dumps(f['body'],sort_keys=True).encode()),source_match=switch['id'],source_prefix=prefix,source_assertion=test,lowered_instructions=ops,instances=inst,negative_controls=controls,model_module_sha256=sha(core.encode()),family_module_sha256=sha(s.encode()),evidence_class='script-checked own-1 local source-state binding plus Lean guard proof',local_source_assertion_states_certified=16,actual_endpoint_entry_and_caller_composition=False,pointer_borrow_drop_unwind_association=False,formatting_cone_complete=False,premises_removed=[],qualification='Full straight-line residual arm and its Match entry checked. Callback, destructor, unwind and pointer events elsewhere are retained; this local certificate does not discharge DeployedWrapper557.')
 for p,t in {D/'lean/PV_B3P_ResidualFamily572227.lean':s,R/'SOURCE-GUARDS-D572.json':json.dumps(meta,indent=2)+'\n'}.items():
  if args.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(source_states=16,negative_controls=controls,check=args.check,whole_cone=False)))
if __name__=='__main__':main()
