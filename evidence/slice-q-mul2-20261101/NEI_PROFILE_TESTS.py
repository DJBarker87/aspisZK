from pathlib import Path
import sys,json,copy,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
import NEI_validate as v
import NEI_field_validate as f
ps=json.loads((E/'NEI_FIELD_PACKETS.json').read_text())
reviews=[f.audit(p,v.neb) for p in ps]
(E/'NEI_FIELD_REVIEW.json').write_text(json.dumps(reviews,indent=2)+'\n')
tests=[]
def reject(name,p,mutate):
 p=copy.deepcopy(p);mutate(p)
 try:f.audit(p,v.neb)
 except (AssertionError,KeyError,ValueError):tests.append(dict(test=name,status='PASS',outcome='rejected'))
 else:raise AssertionError('mutation accepted: '+name)
p=ps[0]
reject('checked equality cannot replace wrapping profile theorem',p,lambda d:d.update(lean_evidence=[e for e in d['lean_evidence'] if not any(t.startswith('NEI_ReleaseField.actual_') for t in e['theorems'])]))
reject('canonical-only native add cannot claim all typed inputs',p,lambda d:d.update(domain='All typed scalar/record inputs; explicit total checked-to-wrapping profile transport.'))
reject('checked fixtures cannot masquerade as wrapping fixtures',p,lambda d:d['release_profile'].update(positive='NEI_N013',negative='NEI_N014'))
p=next(p for p in ps if p['tag']=='cm_mul')
reject('missing sequential canonical cut proof is rejected',p,lambda d:d.update(lean_evidence=[e for e in d['lean_evidence'] if not any(t=='NEI_NEB_CMCalls.multiply' for t in e['theorems'])]))
reject('unrestricted scalar-product theorem cannot discharge full product',p,lambda d:d.update(required_theorems=[t.replace('actual_cm_mul','actual_cm_mul_m31') for t in d['required_theorems']]))
(E/'NEI_PROFILE_TESTS.json').write_text(json.dumps(dict(passed=len(tests),failed=0,tests=tests,checked_and_wrapping_profiles_audited=True,model_packets=len(reviews)),indent=2)+'\n')
print(json.dumps(dict(passed=len(tests),failed=0,field_packets=len(reviews))))
