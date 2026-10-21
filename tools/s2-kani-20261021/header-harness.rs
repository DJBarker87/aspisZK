#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof] #[kani::unwind(10)]
fn header_correspondence() {
    let header:[u8;16]=kani::any();
    let mut proof=[0u8;57607];
    proof[..16].copy_from_slice(&header);
    let magic=header[..8]==compact::MAGIC[..];
    let tail=header[9..].iter().all(|x|*x==0);
    assert_eq!(parse_shape(&proof).is_ok(),header_reference(proof.len(),magic,header[8],tail));
}
#[kani::proof] #[kani::unwind(10)]
fn non_s2_rejected() {
    let tag:u8=kani::any(); kani::assume(tag!=2);
    let mut proof=[0u8;57607];
    proof[..8].copy_from_slice(compact::MAGIC);
    proof[8]=tag;
    assert_eq!(parse_shape(&proof),Err(Error::Parse));
}
#[kani::proof] #[kani::unwind(10)]
fn short_proofs_rejected_without_read() {
    let proof:[u8;16]=kani::any(); let n:usize=kani::any(); kani::assume(n<=16);
    assert_eq!(parse_shape(&proof[..n]),Err(Error::Parse));
}
}
