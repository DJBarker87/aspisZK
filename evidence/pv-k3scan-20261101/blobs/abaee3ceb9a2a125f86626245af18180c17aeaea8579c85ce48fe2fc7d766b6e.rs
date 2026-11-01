//! Raw QM31 bytes and canonicality rejection, including malformed raw limbs.
use aspis_core::field::{QM31,CM31,M31,P};
#[kani::proof]
#[kani::unwind(40)]
fn raw_writer_and_decoder_frame() {
    let words:[u32;4]=kani::any();let mut out:[u8;20]=kani::any();let before=out;
    let q=QM31{c0:CM31::new(M31(words[0]),M31(words[1])),c1:CM31::new(M31(words[2]),M31(words[3]))};
    q.write_le_bytes(&mut out[..16]);
    for i in 0..4 {let bytes=words[i].to_le_bytes();for j in 0..4 {assert_eq!(out[4*i+j],bytes[j]);}}
    assert_eq!(&out[16..],&before[16..]);
    let valid=words[0]<P && words[1]<P && words[2]<P && words[3]<P;
    assert_eq!(QM31::from_le_bytes(&out[..16]),if valid {Some(q)} else {None});
}
