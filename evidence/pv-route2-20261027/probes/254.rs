use aspis_core::field::{M31,CM31,QM31,WideExact,P};
use aspis_core::field::WideExact as E;
pub fn powers<const N:usize>(x:E)->[E;N]{
 let mut out=[E::ZERO;N];
 let mut p=E::ONE;
 let mut i=0usize;
 while i<N {
  out[i]=p;
  i+=1;
  if i<N { p=p.mul(x); }
 }
 out
}
