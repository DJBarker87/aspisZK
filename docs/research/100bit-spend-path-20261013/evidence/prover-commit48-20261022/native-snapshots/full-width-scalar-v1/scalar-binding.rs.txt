// Actual QM31 convenience operation against the owned interpolation scalar.
#[cfg(kani)] mod scalar_proofs {
 use super::field::{QM31,CM31,M31};
 static mut ANSWERS:[u32;4]=[0;4];
 static mut TRACE:[(u32,u32);4]=[(0,0);4];
 static mut NEXT:usize=0;
 fn reset(answers:[u32;4]) {unsafe {ANSWERS=answers;TRACE=[(0,0);4];NEXT=0;}}
 fn trace()->([(u32,u32);4],usize) {unsafe {(TRACE,NEXT)}}
 fn multiply(a:M31,b:M31)->M31 {unsafe {
  let i=NEXT;assert!(i<4);TRACE[i]=(a.0,b.0);NEXT+=1;M31(ANSWERS[i])
 }}
 fn owned(x:QM31,y:M31)->QM31 {
  QM31{c0:CM31{a:x.c0.a.mul(y),b:x.c0.b.mul(y)},c1:CM31{a:x.c1.a.mul(y),b:x.c1.b.mul(y)}}
 }
 #[kani::proof] #[kani::unwind(34)]
 #[kani::stub(crate::field::M31::mul,multiply)]
 fn scalar_call() {
  let a:[u32;4]=kani::any();
  let x=QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};
  let y=M31(kani::any());let answers=kani::any();
  reset(answers);let actual=x.mul_m31(y);let ta=trace();
  reset(answers);let expected=owned(x,y);let tb=trace();
  assert_eq!(actual,expected);assert_eq!(ta,tb);assert_eq!(ta.1,4);
 }
}
