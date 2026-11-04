"""Exact frozen/reference/local-oracle shape; no callee closure inferred."""
from NET_inverse_checks import *

def checked(source,reference):
 frozen=subprocess.check_output(['git','show',REV+':crates/aspis-core/src/field.rs'],cwd=R,text=True)
 fs=functions(frozen);body=fs['try_inv'][0][1]
 count=tok('#[cfg(feature="r0-op-count")] let _count=crate::r0_op_count::enter(crate::r0_op_count::Op::KInv);')
 assert body[:len(count)]==count;body=body[len(count):]
 expected=tok('if self.is_zero(){return None;} let norm=self.c0.square().sub(mul_by_r(self.c1.square())); let inverse_norm=norm.inv(); Some(QM31{c0:self.c0.mul(inverse_norm),c1:self.c1.neg().mul(inverse_norm),})')
 assert body==expected
 assert len([b for _,b in fs['inv'] if b==tok('self.try_inv().expect("cannot invert zero in QM31")')])==1
 fns=functions(source);code=fns['NET_try_inv'][0][1]
 for text in ['#[cfg(NET_bad_argument)] let norm=CM31::ZERO;','#[cfg(NET_bad_reply)] let c0=CM31{a:M31(c0.a.0^1),b:c0.b};']:
  ts=tok(text);hits=[i for i in range(len(code)-len(ts)+1) if code[i:i+len(ts)]==ts];assert len(hits)==1;i=hits[0];code=code[:i]+code[i+len(ts):]
 assert code==tok('if log.zero(x){return None;} let a=log.call(1,x.c0,CM31::ZERO); let b=log.call(1,x.c1,CM31::ZERO); let r=log.call(2,b,CM31::ZERO); let norm=log.call(3,a,r); let inverse_norm=log.call(4,norm,CM31::ZERO); let c0=log.call(5,x.c0,inverse_norm); let neg=log.call(6,x.c1,CM31::ZERO); let c1=log.call(5,neg,inverse_norm); Some(QM31{c0,c1})')
 assert fns['NET_inv'][0][1]==tok('NET_try_inv(x,log).expect("cannot invert zero in QM31")')
 rf=functions(reference)
 assert rf['qm_try_inverse'][0][1]==tok('if O::zero(x){return None;} let norm=O::sub(O::square(x.c0),O::r(O::square(x.c1))); let inverse_norm=O::inverse(norm); Some(Q{c0:O::mul(x.c0,inverse_norm),c1:O::mul(O::neg(x.c1),inverse_norm)})')
 assert rf['qm_inverse'][0][1]==tok('qm_try_inverse::<O>(x).expect("cannot invert zero in QM31")')
 assert not any(t in source for t in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','stub_verified','proof_for_contract'])
 return dict(frozen_revision=REV,frozen_body_tokens_sha256=sha(json.dumps(body)),native_source_sha256=sha(source),reference_sha256=sha(reference),early_zero_call_count=1,nonzero_call_count=9,result_slots=[6,8],full_native_result=False,composed_credit=False,remaining=['Actual child-domain/native/emitted/cohort instantiation','CM31 inverse/M31 inverse ordered-result association','Supplied CM31::square/is_zero and M31::neg slice boundaries'])

def run():
 s=(E/'NET_qinverse.rs.txt').read_text();r=(E/'NET_inverse_reference.rs').read_text();d=checked(s,r);tests=[]
 for name,a,b in [('zero carrier','log.zero(x)','log.zero(QM31::ZERO)'),('norm lhs','log.call(3,a,r)','log.call(3,b,r)'),('inverse argument','log.call(4,norm,','log.call(4,a,'),('conjugation','log.call(6,x.c1,','log.call(6,x.c0,'),('output','Some(QM31{c0,c1})','Some(QM31{c0:c1,c1})'),('error behavior','expect("cannot invert zero in QM31")','unwrap_or(QM31::ZERO)')]:
  assert a in s
  try:checked(s.replace(a,b,1),r)
  except AssertionError:tests.append(dict(name=name,rejected=True))
  else:raise AssertionError('mutation accepted '+name)
 return dict(positive=d,mutations=tests)
if __name__=='__main__':
 d=run();(E/'NET_QINVERSE_SOURCE.json').write_text(json.dumps(d,indent=1)+'\n');print(json.dumps(dict(positive=True,mutations=len(d['mutations']))))
