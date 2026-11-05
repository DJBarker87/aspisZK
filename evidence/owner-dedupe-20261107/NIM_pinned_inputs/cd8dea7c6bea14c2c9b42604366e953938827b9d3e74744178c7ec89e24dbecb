"""Mutation checks add predicates; no inherited validator is weakened."""
from pathlib import Path
import json,copy,contextlib,io
import NGY_validate as v
E=Path(__file__).resolve().parent
original=v.read
cases=[]
def reject(label,transform):
 def mutated(p):
  value=copy.deepcopy(original(p));return transform(Path(p),value)
 v.read=mutated
 try:
  with contextlib.redirect_stdout(io.StringIO()):v.validate(False)
 except (AssertionError,KeyError,ValueError):cases.append(dict(mutation=label,rejected=True))
 else:raise AssertionError('Accepted mutation: '+label)
 finally:v.read=original
reject('reservation exit78',lambda p,x:dict(x,exit=78) if p.name=='NGY_K004-admission.json' else x)
reject('reservation allowed false',lambda p,x:dict(x,reservation=dict(x['reservation'],allowed=False)) if p.name=='NGY_K004-admission.json' else x)
reject('raise memory cap',lambda p,x:dict(x,limits=dict(x['limits'],**{'memory.max':'17179869184'})) if p==E/'NGY_K004/receipt.json' else x)
reject('swap present',lambda p,x:dict(x,swaps='1') if p==E/'NGY_K004/receipt.json' else x)
reject('unfrozen graph',lambda p,x:dict(x,graph_matches_frozen=False) if p.name=='NGY_K004-graph-check.json' else x)
reject('changed lock',lambda p,x:dict(x,unchanged=False) if p.name=='NGY_K004-lock-check.json' else x)
reject('offline disabled',lambda p,x:dict(x,env=dict(x['env'],CARGO_NET_OFFLINE='false')) if p==E/'NGY_K004/receipt.json' else x)
reject('unoptimized build',lambda p,x:dict(x,env=dict(x['env'],CARGO_PROFILE_DEV_OPT_LEVEL='0')) if p==E/'NGY_K004/receipt.json' else x)
reject('control changes target',lambda p,x:dict(x,module='different') if p==E/'NGY_K005/receipt.json' else x)
reject('control passes',lambda p,x:dict(x,exit_status=0) if p==E/'NGY_K005/receipt.json' else x)
reject('nonstandard axiom',lambda p,x:dict(x,print_axioms=["'bad' depends on axioms: [customAxiom]"]) if p==E/'NGY_L001/receipt.json' else x)
reject('source substitution altered',lambda p,x:dict(x,oracle_cut=x['oracle_cut'].replace('Error::Parse','Error::Semantic')) if p.name=='NGY_CUT.json' else x)
reject('inherited source hash changed',lambda p,x:dict(x,inputs={**x['inputs'],next(iter(x['inputs'])):dict(next(iter(x['inputs'].values())),sha256='0'*64)}) if p.name=='NGY_REUSED.json' else x)
(E/'NGY_MUTATIONS.json').write_text(json.dumps(dict(status='PASS',cases=cases),indent=1)+'\n');print(json.dumps(dict(status='PASS',rejected=len(cases))))
# Final closure mutations target native coverage, raw evidence and exact ownership.
final_cases=[]
def reject_final(label,transform):
 def mutated(p):return transform(Path(p),copy.deepcopy(original(p)))
 v.read=mutated
 try:
  with contextlib.redirect_stdout(io.StringIO()):v.validate(True)
 except (AssertionError,KeyError,ValueError):final_cases.append(dict(mutation=label,rejected=True))
 else:raise AssertionError('Accepted final mutation: '+label)
 finally:v.read=original
reject_final('omit native point',lambda p,x:dict(x,pairs=[r for r in x['pairs'] if r['point']!=3]) if p.name=='NGY_NATIVE_MATRIX.json' else x)
reject_final('point5 caller fails',lambda p,x:dict(x,exit_status=1) if p==E/'NGY_K029/receipt.json' else x)
reject_final('field corruption control passes',lambda p,x:dict(x,exit_status=0) if p==E/'NGY_K031/receipt.json' else x)
reject_final('raw root missing',lambda p,x:dict(x,results=x['results'][:-1]) if p==E/'NGY_audit/batch0/proof0.json' else x)
reject_final('raw nonstandard axiom',lambda p,x:dict(x,results=[dict(x['results'][0],walked_axioms=['evilAx'])]+x['results'][1:]) if p==E/'NGY_audit/batch0/proof0.json' else x)
reject_final('planted axiom hidden',lambda p,x:dict(x,results=[dict(x['results'][0],walked_axioms=[])]+x['results'][1:]) if p==E/'NGY_audit/fixtures/fixtures.json' else x)
reject_final('wrong statement owner',lambda p,x:{**x,next(iter(x)):'WrongOwner'} if p.name=='NGY_STATEMENT_ROOTS.json' else x)
reject_final('fixture binary differs',lambda p,x:dict(x,sha256='0'*64) if p==E/'NGY_L024/NGY_ProofDriver_BINARY_PIN.json' else x)
reject_final('missing final combined root',lambda p,x:dict(x,roots=x['roots'][:-1]) if p.name=='NGY_AUDIT_ROOTS.json' else x)
reject_final('status promoted without route',lambda p,x:dict(x,status='CLOSED') if p.name=='NGY_CLOSED.json' else x)
(E/'NGY_MUTATIONS.json').write_text(json.dumps(dict(status='PASS',cases=cases,final_cases=final_cases),indent=1)+'\n');print(json.dumps(dict(status='PASS',rejected=len(cases)+len(final_cases))))
