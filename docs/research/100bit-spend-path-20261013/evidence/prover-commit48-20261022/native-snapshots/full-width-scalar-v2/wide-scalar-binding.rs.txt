#[cfg(kani)] mod wide_scalar_proofs {
 use super::field::{QM31,CM31,M31,WideExact as E,P};
 static mut ANSWERS:[[u32;4];2]=[[0;4];2];
 static mut TRACE:[([u32;4],u32);2]=[([0;4],0);2];
 static mut NEXT:usize=0;
 fn words(x:QM31)->[u32;4] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
 fn qm(a:[u32;4])->QM31 {QM31{c0:CM31{a:M31(a[0]%P),b:M31(a[1]%P)},c1:CM31{a:M31(a[2]%P),b:M31(a[3]%P)}}}
 fn reset(a:[[u32;4];2]) {unsafe {ANSWERS=a;TRACE=[([0;4],0);2];NEXT=0;}}
 fn trace()->([([u32;4],u32);2],usize) {unsafe {(TRACE,NEXT)}}
 fn multiply(x:QM31,y:M31)->QM31 {unsafe {let i=NEXT;assert!(i<2);TRACE[i]=(words(x),y.0);NEXT+=1;qm(ANSWERS[i])}}
 #[kani::proof] #[kani::unwind(34)]
 #[kani::stub(crate::field::QM31::mul_m31,multiply)]
 fn full_width_scalar() {
  let lo=qm(kani::any());let hi=qm(kani::any());let x=E::new(lo,hi);let raw:u32=kani::any();let answers=kani::any();
  reset(answers);let actual=x.mul_m31(M31(raw));let ta=trace();
  reset(answers);let y=M31(raw%P);let lo=multiply(lo,y);let hi=multiply(hi,y);let expected=E::new(lo,hi);let tb=trace();
  assert_eq!(actual,expected);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
}
