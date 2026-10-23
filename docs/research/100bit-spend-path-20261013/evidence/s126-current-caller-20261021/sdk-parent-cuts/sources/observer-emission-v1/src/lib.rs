#![allow(dead_code,unexpected_cfgs)]
static mut OBSERVED: usize = 0;
#[inline(never)]
fn observer() -> Option<fn()> { None }
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 fn literal_none_after_mutable_zero_write() {
  let value:usize=kani::any();
  unsafe { OBSERVED=value; }
  assert!(observer().is_none(), "literal None is independent of mutable zero static");
  assert_eq!(unsafe { OBSERVED },value);
 }
}
