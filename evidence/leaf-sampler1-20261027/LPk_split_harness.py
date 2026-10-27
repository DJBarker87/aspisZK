"""Isolate failed gates; never retry an unchanged timed-out harness."""
import subprocess,difflib
from pathlib import Path
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
f=B+'/LPk_src/crates/aspis-r1-cost-probe/src/LPk_harness.rs'
s=subprocess.check_output(['ssh',H,'cat '+f],text=True)
s=s.replace('kani::assume(u64::from(q) * u64::from(P) + r == (remainder << 32) | u64::from(limb));','kani::assume(u128::from(q) * u128::from(P) + u128::from(r) == u128::from((remainder << 32) | u64::from(limb)));')
s+='''
// Split K005: isolate the quotient cast bound, remainder bound, and
// reconstruction before narrowing. No division-equivalence goal.
#[kani::proof]
fn LPk_quotient_bound() {
 let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));
 let n=(rem<<32)|u64::from(limb);
 let q=n/u64::from(P);
 assert!(q<=u64::from(u32::MAX));
}
#[kani::proof]
fn LPk_remainder_bound() {
 let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));
 let n=(rem<<32)|u64::from(limb);
 let r=n%u64::from(P);
 assert!(r<u64::from(P));
}
#[kani::proof]
fn LPk_reconstruction() {
 let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));
 let n=(rem<<32)|u64::from(limb);
 let q=n/u64::from(P);let r=n%u64::from(P);
 assert_eq!(u128::from(q)*u128::from(P)+u128::from(r),u128::from(n));
}
// Split K006: order and final store, without reasserting the arithmetic
// relation supplied by the paired stub. Wide relation avoids irrelevant
// checked-u64 arithmetic in the specification itself.
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(LPk_step, LPk_step_relation)]
fn LPk_reverse_order() {
 let mut quotient:[u32;8]=kani::any();let original=quotient;
 let mut remainder=0u64;let mut count=0usize;
 for limb in quotient.iter_mut().rev() {
  assert_eq!(*limb,original[7-count]);
  let(q,r)=LPk_step(remainder,*limb);*limb=q;remainder=r;count+=1;
 }
 assert_eq!(count,8);
}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(LPk_step, LPk_step_relation)]
fn LPk_reverse_store() {
 let mut quotient:[u32;8]=kani::any();let mut qs=[0u32;8];
 let mut remainder=0u64;let mut count=0usize;
 for limb in quotient.iter_mut().rev() {
  let(q,r)=LPk_step(remainder,*limb);*limb=q;remainder=r;qs[count]=q;count+=1;
 }
 let at:usize=kani::any();kani::assume(at<8);
 assert_eq!(quotient[7-at],qs[at]);
 assert!(remainder<u64::from(P));
}
'''
subprocess.run(['ssh',H,'cat > '+f],input=s,text=True,check=True)
path='crates/aspis-r1-cost-probe/src/sampler.rs';a=subprocess.check_output(['git','show','4bb3b3f:'+path],text=True);b=subprocess.check_output(['ssh',H,'cat '+B+'/LPk_src/'+path],text=True)
patch=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+path,tofile='b/'+path))+''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/LPk_harness.rs'))
(E/'LPk_harness.patch').write_text(patch)
