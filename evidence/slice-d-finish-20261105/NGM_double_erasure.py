from pathlib import Path
import json,subprocess,re,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());src=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
def fn(s,n):
 a=s.index(n);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
frozen=fn(src,'pub fn double(');actual=fn(x['crates/aspis-r1-cost-probe/src/NGM_weights.rs'],'fn source_double(')
def erase(s):
 assert s.count('opaque_product(x,x,log)')==2
 return re.sub(r'\s+','',s.replace('fn source_double(x:K,log:&mut ProductLog)','pub fn double(x:K)').replace('opaque_product(x,x,log)','x.mul(x)'))
assert erase(actual)==re.sub(r'\s+','',frozen)
mut=[]
for old,new in [('opaque_product(x,x,log)','opaque_product(K::ZERO,x,log)'),('.add(','.sub('),('K::ONE','K::ZERO')]:
 changed=actual.replace(old,new,1)
 try:accepted=erase(changed)==re.sub(r'\s+','',frozen)
 except AssertionError:accepted=False
 assert not accepted;mut.append(dict(change=[old,new],rejected=True))
(E/'NGM_DOUBLE_ERASURE.json').write_text(json.dumps(dict(status='PASS source erasure only',frozen_body_sha256=hashlib.sha256(frozen.encode()).hexdigest(),instrumented_body_sha256=hashlib.sha256(actual.encode()).hexdigest(),products=2,mutations=mut),indent=2)+'\n')
print('PASS double source erasure and 3 mutations')
