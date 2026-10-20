#[inline(always)]
pub fn value(tag: u16, index: usize, x: E) {
    #[cfg(feature="prover")]
    VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));
    #[cfg(not(feature="prover"))]
    let _ = (tag,index,x);
}