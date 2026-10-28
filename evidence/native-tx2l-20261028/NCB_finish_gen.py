from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/fast_dots.rs'
t=r'''
#[cfg(kani)] mod NCB_finish {
 use super::*;
 static mut CALLS:u8=0;static mut OUTPUT:[u32;8]=[0;8];
 fn finish(t:EbyKDot)->WideExact {unsafe{
  assert!(CALLS==0);CALLS=1;assert!(crate::fast_pairing::NBQ_count(&t)==3);assert!(crate::fast_pairing::NCB_invariant(&t));
  let raw:[u32;8]=kani::any();for j in 0..8{kani::assume(raw[j]<2147483647);OUTPUT[j]=raw[j];}
  WideExact::from_limbs(raw).unwrap()
 }}
 fn source(value:WideExact,tail:EbyKDot)->WideExact{value.add(tail.finish())}
 #[kani::proof] #[kani::unwind(512)] ATTR #[kani::stub(EbyKDot::finish,finish)]
 fn continuation(){
  let raw:[u32;8]=kani::any();for j in 0..8{kani::assume(raw[j]<2147483647);}
  let value=WideExact::from_limbs(raw).unwrap();let tail=crate::fast_pairing::NBQ_state(3);kani::assume(crate::fast_pairing::NCB_invariant(&tail));
  unsafe{CALLS=0;}let out=source(value,tail).to_limbs();let j:usize=kani::any();kani::assume(j<8);
  unsafe{assert!(CALLS==1);assert!(u64::from(out[j])==(u64::from(raw[j])+u64::from(OUTPUT[j]))%2147483647);}
 }
}
'''.replace('ATTR',attrs)
emit(p,t,'NCB_finish')
