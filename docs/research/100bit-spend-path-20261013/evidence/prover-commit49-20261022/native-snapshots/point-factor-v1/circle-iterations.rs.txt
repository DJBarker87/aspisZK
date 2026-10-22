
fn double_e(x:E)->E {x.mul(x).add(x.mul(x)).sub(E::ONE)}
fn native_circle_fill(mut factors:[[[E;4];5];5],k:usize,d:usize,mut x:E)->([[[E;4];5];5],E) {
 let y=double_e(x);factors[3+k][d]=[E::ONE,x,y,x.mul(y)];x=double_e(y);(factors,x)
}
fn owner_circle_fill(mut out:[[E;4];5],d:usize,x:E)->([[E;4];5],E) {
 let y=double_e(x);out[d]=[E::ONE,x,y,x.mul(y)];let next=double_e(y);(out,next)
}
fn native_point_factor(a:E,b:E)->[E;4] {
 [E::ONE.sub(a).mul(E::ONE.sub(b)),a.mul(E::ONE.sub(b)),E::ONE.sub(a).mul(b),a.mul(b)]
}
fn owner_point_factor(a:E,b:E)->[E;4] {
 [E::ONE.sub(a).mul(E::ONE.sub(b)),a.mul(E::ONE.sub(b)),E::ONE.sub(a).mul(b),a.mul(b)]
}
#[cfg(kani)] mod circle_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(128)] fn factor_fill_transition() {
  let factors:[[[E;4];5];5]=unsafe {core::mem::transmute(kani::any::<[u32;100]>())};
  let k:usize=kani::any();let d:usize=kani::any();kani::assume(k<2 && d>0 && d<5);
  let x=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_circle_fill(factors,k,d,x);let ta=trace();
  reset(answers);let row=owner_circle_fill(factors[3+k],d,x);let tb=trace();
  let mut b=factors;b[3+k]=row.0;
  assert_eq!(a,(b,row.1));assert_eq!(ta,tb);assert_eq!(ta.1,9);
 }
 #[kani::proof] #[kani::unwind(128)] fn point_factor_expression() {
  let a=E(kani::any());let b=E(kani::any());let answers=kani::any();
  reset(answers);let x=native_point_factor(a,b);let tx=trace();
  reset(answers);let y=owner_point_factor(a,b);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,8);
 }
}
