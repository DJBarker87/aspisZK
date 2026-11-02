"""Check one generic residual-constructor shape across all sixteen instances.

Pure enum construction/projection/discriminant only. The source's destructor,
restoration and unwind operations are kept outside this local claim.
"""
from pathlib import Path
import json,lzma,hashlib,argparse
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());f=fs[370];statements={}
def visit(v):
 if isinstance(v,list):
  for y in v:visit(y)
 elif isinstance(v,dict):
  if {'span','id','kind'}<=v.keys():statements[v['id']]=v
  for y in v.values():visit(y)
visit(f['body'])
# Exact statement chain: Break(x), Break(Break(x)), inner residual payload,
# discriminant, equality to variant 1, then the MIR assertion.
chain=[24818,24819,24825,24828,24829,24831]
s=[statements[i]for i in chain];assign=lambda st:st['kind']['Assign']
lhs,rhs=assign(s[0]);assert lhs['kind']=={'Local':18};adt,fields=rhs['Aggregate'];assert adt['Adt'][0]['id']=={'Adt':17}and adt['Adt'][1]==1 and len(fields)==1
lhs,rhs=assign(s[1]);assert lhs['kind']=={'Local':7};adt,fields=rhs['Aggregate'];assert adt['Adt'][0]['id']=={'Adt':17}and adt['Adt'][1]==1 and fields[0]['Move']['kind']=={'Local':18}
lhs,rhs=assign(s[2]);assert lhs['kind']=={'Local':13};place=rhs['Use'][0]['Move']['kind']['Projection'];assert place[0]['kind']=={'Local':7}and place[1]=={'Field':[{'Adt':[17,1]},0]}
lhs,rhs=assign(s[3]);assert lhs['kind']=={'Local':31}and rhs['Discriminant']['kind']=={'Local':13}
lhs,rhs=assign(s[4]);assert lhs['kind']=={'Local':33};op,left,right=rhs['BinaryOp'];assert op=='Eq'and left['Copy']['kind']=={'Local':31}and right['Const']['kind']['Literal']['Scalar']['Signed']==['Isize','1']
assert s[5]['kind']['Assert']['assert']['cond']['Move']['kind']=={'Local':33}and s[5]['kind']['Assert']['assert']['expected']is True
# Pin the whole body. The checked constructor/projection chain is an invariant
# of the residual arm, not a claim about arbitrary variants arriving from callers.
instances=[dict(instance=k,environment=v['environment'],statement=24831,lemma='PV_B3P_ControlFlowAssertion571227.constructed_assertion')for k,v in g['instances'].items()if v['id']==370];assert len(instances)==16
x=dict(llbc_sha256=hashlib.sha256(raw).hexdigest(),source_body_sha256=hashlib.sha256(json.dumps(f['body'],sort_keys=True).encode()).hexdigest(),statement_chain=s,instances=instances,scope='local enum constructor/projection law only; complete source-state/caller and drop/unwind association OPEN',evidence_class='script-checked structural source shape and generic Lean constructor law',premises_removed=[])
p=R/'CONTROLFLOW-ASSERTIONS-D571.json';s=json.dumps(x,indent=2)+'\n'
if args.check:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(instances=len(instances),generic_constructor_chain=chain,check=args.check)))
