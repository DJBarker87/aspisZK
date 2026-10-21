#![allow(dead_code)]
fn header_reference(length:usize,magic:bool,tag:u8,tail:bool)->bool{length==57607&&magic&&tag==2&&tail}
#[cfg(kani)] mod proofs {
use aspis_r1_cost_probe::{verifier,compact};
#[kani::proof] #[kani::unwind(10)] fn frozen_header_reference(){
let header:[u8;16]=kani::any();let mut proof=[0u8;57607];proof[..16].copy_from_slice(&header);
assert_eq!(verifier::PROOF_BYTES,57607);assert_eq!(compact::MAGIC,b"R1P3CB18");
let actual=verifier::parse_shape(&proof);
let expected=super::header_reference(proof.len(),header[..8]==compact::MAGIC[..],header[8],header[9..].iter().all(|x|*x==0));
assert_eq!(actual.is_ok(),expected);
if let Ok(variant)=actual{assert_eq!(variant.tag(),2);}
}
#[kani::proof] #[kani::unwind(10)] fn frozen_header_rejects_non_s2(){
let tag:u8=kani::any();kani::assume(tag!=2);let mut proof=[0u8;57607];proof[..8].copy_from_slice(compact::MAGIC);proof[8]=tag;
assert!(verifier::parse_shape(&proof).is_err());
}
}
