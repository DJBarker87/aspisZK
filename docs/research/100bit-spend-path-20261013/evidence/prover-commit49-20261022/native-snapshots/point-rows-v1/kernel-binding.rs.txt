
fn sq_k(x:E)->E {call(5,x,E(0))}
fn neg_k(x:E)->E {call(6,x,E(0))}
fn inv_m(x:E)->E {call(7,x,E(0))}
fn r_c(x:E)->E {call(8,x,E(0))}
fn inv_c(x:E)->E {call(9,x,E(0))}
fn native_pow_step(mut base:E,mut exp:u64,mut acc:E)->(E,u64,E) {
 if exp>0 {if exp&1==1 {acc=acc.mul(base);}base=sq_k(base);exp>>=1;}
 (base,exp,acc)
}
fn owner_pow_step(base:E,exp:u8,acc:E)->(E,u8,E) {
 if exp==0 {(base,exp,acc)} else {
 let next=if exp&1!=0 {acc.mul(base)} else {acc};
 let q=sq_k(base);(q,exp>>1u32,next)
 }
}
fn native_c_inverse(a:E,b:E)->(E,E) {
 let norm=a.mul(a).add(b.mul(b));let inv_norm=inv_m(norm);
 (a.mul(inv_norm),neg_k(b).mul(inv_norm))
}
fn owner_c_inverse(a:E,b:E)->(E,E) {
 let norm=a.mul(a).add(b.mul(b));let inv_norm=inv_m(norm);
 (a.mul(inv_norm),neg_k(b).mul(inv_norm))
}
fn native_q_inverse(a:E,b:E,zero:bool)->Option<(E,E)> {
 if zero {return None;}
 let norm=sq_k(a).sub(r_c(sq_k(b)));let inverse_norm=inv_c(norm);
 Some((a.mul(inverse_norm),neg_k(b).mul(inverse_norm)))
}
fn owner_q_inverse(a:E,b:E,zero:bool)->Option<(E,E)> {
 if zero {None} else {
 let norm=sq_k(a).sub(r_c(sq_k(b)));let ni=inv_c(norm);
 Some((a.mul(ni),neg_k(b).mul(ni)))
 }
}
#[cfg(kani)] mod kernel_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(20)] fn native_kernel_transitions() {
  let a=E(kani::any());let b=E(kani::any());let answers=kani::any();
  let exp:u64=kani::any();kani::assume(exp<=255);let acc=E(kani::any());let zero:bool=kani::any();
  reset(answers);let x=native_pow_step(a,exp,acc);let tx=trace();
  reset(answers);let y=owner_pow_step(a,exp as u8,acc);let ty=trace();
  assert_eq!(x,(y.0,y.1 as u64,y.2));assert_eq!(tx,ty);
  reset(answers);let x=native_c_inverse(a,b);let tx=trace();
  reset(answers);let y=owner_c_inverse(a,b);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,7);
  reset(answers);let x=native_q_inverse(a,b,zero);let tx=trace();
  reset(answers);let y=owner_q_inverse(a,b,zero);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,if zero {0}else{8});
 }
}
