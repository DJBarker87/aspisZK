from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());code=inputs['crates/aspis-r1-cost-probe/src/NGM_helpers.rs'];frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
def body(text,name):
 start=text.index('fn '+name+'(');lo=text.index('{',start);depth=1;i=lo+1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[start:i]
norm=lambda s:re.sub(r'\s+','',s)
def round_erased(s):
 return norm(s.replace('source_round','finish_relation_round').replace(',log:&mut RoundLog','').replace('scale(claim,QUARTER,log)','claim.mul_m31(QUARTER)').replace('polynomial_reply(poly,alpha,log)','polynomial(poly,alpha)'))
actual=body(frozen,'finish_relation_round');instrumented=body(code,'source_round');assert round_erased(instrumented)==norm(actual)
step=body(code,'source_polynomial_step');expression=step[step.index('{')+1:-1];erased=expression.replace('product(a,x,log)','a.mul(x)').replace('coefficient(bytes,i,log)','field(bytes,i)');poly=body(frozen,'polynomial');assert norm(erased)=='a.mul(x).add(field(bytes,i))'and norm(erased)in norm(poly)
mutations=[]
for old,new in [('lhs!=rhs','lhs==rhs'),('Error::Relation','Error::Parse'),('QUARTER','M31::ZERO')]:
 assert old in instrumented;mutations.append(dict(target='round',change=[old,new],rejected=round_erased(instrumented.replace(old,new,1))!=norm(actual)))
for old,new in [('product(a,x,log)','product(a,a,log)'),('coefficient(bytes,i,log)','coefficient(bytes,i+1,log)'),('.add(','.sub(')]:
 bad=expression.replace(old,new,1).replace('product(a,x,log)','a.mul(x)').replace('coefficient(bytes,i,log)','field(bytes,i)');mutations.append(dict(target='polynomial-step',change=[old,new],rejected=norm(bad)!=norm(erased)))
assert all(m['rejected']for m in mutations)
(E/'NGM_HELPER_ERASURE.json').write_text(json.dumps(dict(status='PASS source erasure only; no cohort or native credit',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',round_sha256=hashlib.sha256(actual.encode()).hexdigest(),polynomial_sha256=hashlib.sha256(poly.encode()).hexdigest(),round_opaque_sites=2,polynomial_opaque_sites=2,mutations=mutations),indent=2)+'\n')
print(json.dumps(dict(status='PASS erasure',mutations=len(mutations))))
