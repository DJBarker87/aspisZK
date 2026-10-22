#![allow(dead_code,unexpected_cfgs)]
use aspis_s126_sdk_proof_gate::prefix_different;
extern "C" {#[link_name="memcmp"] fn native_memcmp(left:*const u8,right:*const u8,length:usize)->i32;}
#[cfg_attr(kani,kani::requires(!prefix_different(left,right)))]
#[cfg_attr(kani,kani::modifies())]
#[cfg_attr(kani,kani::ensures(|result| *result==0))]
pub fn equal_memcmp(left:&[u8;688],right:&[u8;688])->i32 {
 unsafe{native_memcmp(left.as_ptr(),right.as_ptr(),688)}
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(equal_memcmp)] #[kani::unwind(700)]
 fn native_equal_arrays_memcmp() {
  let left:[u8;688]=kani::any();let right=left;
  let alias:bool=kani::any();
  let selected=if alias {&left}else{&right};
  let actual=equal_memcmp(&left,selected);
  assert_eq!(actual,0);
  kani::cover!(alias,"same-pointer equal688-byte regions");
  kani::cover!(!alias,"distinct equal688-byte regions");
 }
}
