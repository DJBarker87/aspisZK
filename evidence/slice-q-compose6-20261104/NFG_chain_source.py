"""Reverse only the declared opaque call cuts. Generic fn dispatch earns no credit."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def body(s,marker):
 i=s.index('{',s.index(marker));j=i;depth=1
 while depth:
  j+=1;depth+=(s[j]=='{')-(s[j]=='}')
 return s[i:j+1]
def norm(s):
 s=re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
 return re.sub(r',([}])',r'\1',s)
def check(source=None):
 source=(E/'NFG_chain.rs.txt').read_text() if source is None else source
 frozen=subprocess.check_output(['git','show',REV+':crates/aspis-core/src/field.rs'],cwd=R,text=True)
 cm=frozen[frozen.index('impl CM31 {'):frozen.index('impl QM31 {')]
 qm=frozen[frozen.index('impl QM31 {'):]
 rules={
 'cm_fixed':('pub fn inv_with',cm,[('l.m(0,x.a,x.a)','self.a.mul(self.a)'),('l.m(0,x.b,x.b)','self.b.mul(self.b)'),('l.m(1,norm,M31(0))','inverse(norm)'),('l.m(0,x.a,inv_norm)','self.a.mul(inv_norm)'),('l.m(0,x.b.neg(),inv_norm)','self.b.neg().mul(inv_norm)')]),
 'square':('pub fn square',qm,[('l.c(2,x.c0,CM31::ZERO)','self.c0.square()'),('l.c(2,x.c1,CM31::ZERO)','self.c1.square()'),('l.c(3,x.c0,x.c1)','self.c0.mul(self.c1)')]),
 'try_inv':('pub fn try_inv',qm,[('l.c(2,x.c0,CM31::ZERO)','self.c0.square()'),('l.c(2,x.c1,CM31::ZERO)','self.c1.square()'),('l.c(4,norm,CM31::ZERO)','norm.inv()'),('l.c(3,x.c0,inverse_norm)','self.c0.mul(inverse_norm)'),('l.c(3,x.c1.neg(),inverse_norm)','self.c1.neg().mul(inverse_norm)')])}
 out=[]
 for name,(marker,forest,replacements) in rules.items():
  actual=body(source,'fn '+name+'(')
  for old,new in replacements:assert actual.count(old)==1,(name,old);actual=actual.replace(old,new)
  actual=actual.replace('super::super::mul_by_r','mul_by_r').replace('x.is_zero()','self.is_zero()').replace('x.c1.neg()','self.c1.neg()')
  expected=body(forest,marker)
  expected=re.sub(r'#\[cfg\(feature = "r0-op-count"\)\]\s*let _count = crate::r0_op_count::enter\([^;]*;', '',expected)
  expected=expected.replace('Some(Self {','Some(QM31{')
  assert norm(actual)==norm(expected),(name,'frozen cut reversal mismatch',actual,expected)
  out.append(dict(cut=name,frozen_body_sha256=hashlib.sha256(body(forest,marker).encode()).hexdigest(),opaque_sites=len(replacements),status='G/window only; missing child laws remain OPEN'))
 assert re.search(r'\b(?:static|unsafe)\b',source) is None and re.search(r'\bfn\s*\(',source) is None
 return dict(cuts=out,generic_inv_with='QUARANTINED; fixed CM31::inv edge only; no function pointer is compared or executed by these G windows',remaining='outside-Q packet domains, callee semantics/error association; no inverse root closure')
if __name__=='__main__':print(json.dumps(check(),indent=2))
