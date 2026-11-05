use super::*;

#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_finish() {
    let accepted: [u32; 22] = kani::any();
    let len: usize = kani::any();
    let draws: usize = kani::any();
    let k: usize = kani::any();
    kani::assume(len <= 22 && draws <= 64 && k < 22);
    let out = QueryScan { accepted, accepted_len: len, draws }.finish();
    let correct = match out {
        Ok(q) => len == 22 && q[k] == accepted[k],
        Err(QuerySampleError::DrawLimitExhausted { accepted: n, max_draws }) =>
            len != 22 && n == len && max_draws == 64,
        _ => false,
    };
    #[cfg(not(NGQ_invert))] assert!(correct);
    #[cfg(NGQ_invert)] assert!(!correct);
}

#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_query_words() {
    let block: [u8;32] = kani::any();
    let k: usize = kani::any(); kani::assume(k < 8);
    let out = query_words(&block);
    let j=4*k;
    let expected = ((block[j] as u32) | ((block[j+1] as u32)<<8)
       | ((block[j+2] as u32)<<16) | ((block[j+3] as u32)<<24)) & 262143;
    let correct = out[k] == expected && out[k] < 262144;
    #[cfg(not(NGQ_invert))] assert!(correct);
    #[cfg(NGQ_invert)] assert!(!correct);
}
