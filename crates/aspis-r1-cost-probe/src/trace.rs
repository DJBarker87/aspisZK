//! UNPROVED COST PROBE. Native byte traces; compiled out of SBF.
use aspis_core::field::WideExact as E;
#[cfg(feature="prover")]
std::thread_local! { static VALUES: std::cell::RefCell<alloc::vec::Vec<(u16,usize,[u8;32])>> = const { std::cell::RefCell::new(alloc::vec::Vec::new()) }; }
#[inline(always)]
pub fn value(tag: u16, index: usize, x: E) {
    #[cfg(feature="prover")]
    VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));
    #[cfg(not(feature="prover"))]
    let _ = (tag,index,x);
}
#[cfg(feature="prover")]
pub fn take() -> alloc::vec::Vec<(u16,usize,[u8;32])> {
    VALUES.with(|v| core::mem::take(&mut *v.borrow_mut()))
}
