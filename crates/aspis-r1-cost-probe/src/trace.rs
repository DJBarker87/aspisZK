//! UNPROVED COST PROBE. Native byte traces; compiled out of SBF.
use aspis_core::field::WideExact as E;
#[cfg(all(feature="prover", not(feature="ct-host-prover")))]
std::thread_local! { static VALUES: std::cell::RefCell<alloc::vec::Vec<(u16,usize,[u8;32])>> = const { std::cell::RefCell::new(alloc::vec::Vec::new()) }; }
#[inline(always)]
pub fn value(tag: u16, index: usize, x: E) {
    #[cfg(all(feature="prover", not(feature="ct-host-prover")))]
    VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));
    #[cfg(any(not(feature="prover"), feature="ct-host-prover"))]
    let _ = (tag,index,x);
}
#[cfg(all(feature="prover", not(feature="ct-host-prover")))]
pub fn take() -> alloc::vec::Vec<(u16,usize,[u8;32])> {
    VALUES.with(|v| core::mem::take(&mut *v.borrow_mut()))
}

#[cfg(all(feature="prover", feature="ct-host-prover"))]
pub fn take() -> alloc::vec::Vec<(u16,usize,[u8;32])> { alloc::vec::Vec::new() }
