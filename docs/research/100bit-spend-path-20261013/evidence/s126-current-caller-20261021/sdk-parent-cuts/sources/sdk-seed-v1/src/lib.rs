#![allow(dead_code,unexpected_cfgs)]
pub fn seed_byte(original:u8,candidate:u8,index:usize)->u8 {
 if index<688 {candidate} else if index==696 {2} else {original}
}
#[cfg(kani)] struct Ghost<T>{value:T,tag:u64}
#[cfg(kani)] static mut OBSERVED:Ghost<usize>=Ghost{value:0,tag:0x51a3000000000001};
#[cfg(kani)] static mut EXPECTED:Ghost<u8>=Ghost{value:0,tag:0x51a3000000000002};
#[cfg(kani)] fn observed()->usize {unsafe{OBSERVED.value}}
#[cfg(kani)] fn expected()->u8 {unsafe{EXPECTED.value}}
#[cfg_attr(kani,kani::requires(observed()<58295))]
#[cfg_attr(kani,kani::requires(expected()==seed_byte(bytes[observed()],if observed()<688 {candidate[observed()]}else{0},observed())))]
#[cfg_attr(kani,kani::modifies(bytes.as_mut_ptr().cast::<[u8;688]>(),unsafe{bytes.as_mut_ptr().add(696)}))]
#[cfg_attr(kani,kani::ensures(|_| bytes[observed()]==expected()))]
pub fn native_seed(bytes:&mut [u8;58295],candidate:&[u8;688]) {
 unsafe{core::ptr::copy_nonoverlapping(candidate.as_ptr(),bytes.as_mut_ptr(),688);}
 bytes[696]=2;
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_seed)] #[kani::unwind(8)]
 fn native_seed_byte_and_frame() {
  let mut bytes:[u8;58295]=kani::any();let candidate:[u8;688]=kani::any();
  let index:usize=kani::any();kani::assume(index<58295);
  let old=bytes[index];let selected=if index<688 {candidate[index]}else{0};
  let want=seed_byte(old,selected,index);
  unsafe{OBSERVED.value=index;EXPECTED.value=want;}
  native_seed(&mut bytes,&candidate);
  assert_eq!(bytes[index],want);
  kani::cover!(index==0,"prefix begins");
  kani::cover!(index==687,"prefix ends");
  kani::cover!(index==696,"tag cell");
  kani::cover!(index==58294,"last unchanged byte");
 }
}
