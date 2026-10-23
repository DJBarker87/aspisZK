#![allow(dead_code,unexpected_cfgs)]
pub fn seed_byte(original:u8,candidate:u8,index:usize)->u8 {
 if index<688 {candidate} else if index==696 {2} else {original}
}
#[cfg(kani)] struct Ghost<T>{value:T,tag:u64}
#[cfg(kani)] static mut OBSERVED:Ghost<usize>=Ghost{value:0,tag:0x51a3000000000001};
#[cfg(kani)] static mut EXPECTED:Ghost<u8>=Ghost{value:0,tag:0x51a3000000000002};
#[cfg(kani)] fn observed()->usize {unsafe{OBSERVED.value}}
#[cfg(kani)] fn expected()->u8 {unsafe{EXPECTED.value}}
fn prefix_value(bytes:&[u8;58295],index:usize)->u8 {
  let prefix=unsafe{core::ptr::read(bytes.as_ptr().cast::<[u8;688]>())};
  prefix[index]
}
#[cfg_attr(kani,kani::requires(observed()<688))]
#[cfg_attr(kani,kani::requires(expected()==candidate[observed()]))]
#[cfg_attr(kani,kani::modifies(bytes.as_mut_ptr().cast::<[u8;688]>(),unsafe{bytes.as_mut_ptr().add(696)}))]
#[cfg_attr(kani,kani::ensures(|_| prefix_value(bytes,observed())==expected() && bytes[696]==2))]
pub fn native_seed(bytes:&mut [u8;58295],candidate:&[u8;688]) {
 unsafe{core::ptr::copy_nonoverlapping(candidate.as_ptr(),bytes.as_mut_ptr(),688);}
 bytes[696]=2;
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_seed)] #[kani::unwind(8)]
 fn native_seed_byte_and_frame() {
  let mut bytes:[u8;58295]=kani::any();let candidate:[u8;688]=kani::any();
  let index:usize=kani::any();kani::assume(index<688);
  let old=0;let selected=candidate[index];
  let want=seed_byte(old,selected,index);
  unsafe{OBSERVED.value=index;EXPECTED.value=want;}
  native_seed(&mut bytes,&candidate);
  assert_eq!(prefix_value(&bytes,index),want);assert_eq!(bytes[696],2);
  kani::cover!(index==0,"prefix begins");
  kani::cover!(index==687,"prefix ends");
 }
}
