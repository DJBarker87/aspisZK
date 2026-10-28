use aspis_core::Digest32;
static mut EXPECT_PARTS: *const () = core::ptr::null();
static mut EXPECT_LEN: usize = 0;
static mut REPLY: [u8;32] = [0;32];
static mut CALLS: usize = 0;
fn runtime_hashv(parts: &[&[u8]]) -> solana_program::hash::Hash {
    unsafe {
        assert!(parts.as_ptr().cast::<()>() == EXPECT_PARTS);
        assert!(parts.len() == EXPECT_LEN);
        CALLS += 1;
        solana_program::hash::Hash::new_from_array(REPLY)
    }
}
#[kani::proof]
#[kani::stub(solana_program::hash::hashv, runtime_hashv)]
fn NBG_digest_reply() {
    let a: [u8;32] = kani::any();
    let b: [u8;32] = kani::any();
    let n:usize=kani::any(); let m:usize=kani::any();
    kani::assume(n<=32 && m<=32);
    let parts: [&[u8];2]=[&a[..n],&b[..m]];
    let reply: [u8;32]=kani::any();
    unsafe { EXPECT_PARTS=parts.as_ptr().cast::<()>(); EXPECT_LEN=2; REPLY=reply; CALLS=0; }
    let out=super::SolanaDigest.digest(&parts);
    let i:usize=kani::any(); kani::assume(i<32);
    assert!(out[i]==reply[i]);
    unsafe {assert!(CALLS==1);}
    kani::cover!(n==0 && m==32);
}
