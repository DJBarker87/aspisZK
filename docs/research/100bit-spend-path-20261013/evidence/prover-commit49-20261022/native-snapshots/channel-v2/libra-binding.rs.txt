
fn power_call(x:E,n:u64)->E {assert!(n<=255);call(10,x,E(n as u32))}
fn native_libra(extra:[E;2],j:usize)->E {
 if j<56 {power_call(extra[j/28],(j%28) as u64)} else {E(0)}
}
fn owner_libra(extra:[E;2],j:usize)->E {
 if j<56 {power_call(extra[j/28],((j%28) as u8) as u64)} else {E(0)}
}
fn lift_c(x:E)->E {call(11,x,E(0))}
fn lift_q(x:E)->E {call(12,x,E(0))}
fn native_half()->E {lift_q(lift_c(inv_m(E(2))))}
fn owner_half()->E {let m=inv_m(E(2));let c=lift_c(m);lift_q(c)}
#[cfg(kani)] mod libra_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(20)] fn libra_half_callers() {
  let extra=[E(kani::any()),E(kani::any())];let j:usize=kani::any();let answers=kani::any();
  reset(answers);let x=native_libra(extra,j);let tx=trace();
  reset(answers);let y=owner_libra(extra,j);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,if j<56 {1}else{0});
  reset(answers);let x=native_half();let tx=trace();
  reset(answers);let y=owner_half();let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,3);
 }
}
