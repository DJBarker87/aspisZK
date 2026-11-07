use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::modifies()]
#[kani::ensures(|out| out.is_ok())]
fn NMD_shape(_frame:&mut u8)->Result<Box<u8>,Error> {Ok(Box::new(7))}
#[kani::modifies()]
#[kani::ensures(|out| !(out.is_ok()))]
fn NMD_inverse_shape(_frame:&mut u8)->Result<Box<u8>,Error> {Ok(Box::new(7))}
#[kani::modifies()]
#[kani::ensures(|out| out.is_ok())]
fn NMD_modifies_shape(frame:&mut u8)->Result<Box<u8>,Error> {*frame=1;Ok(Box::new(7))}
#[kani::proof_for_contract(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_contract() {let mut frame=0;NMD_shape(&mut frame);}
#[kani::proof_for_contract(NMD_inverse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_inverse() {let mut frame=0;NMD_inverse_shape(&mut frame);}
#[kani::proof_for_contract(NMD_modifies_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_modifies() {let mut frame=0;NMD_modifies_shape(&mut frame);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_real() {let mut frame=0;let r=NMD_shape(&mut frame);assert_eq!(r.unwrap().as_ref(),&7);}
#[kani::proof]
#[kani::stub_verified(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_unimplied() {let mut frame=0;let r=NMD_shape(&mut frame);assert_eq!(r.unwrap().as_ref(),&7);}
// Exact deployed enum coverage; feature prover is disabled in deployed receipts.
impl kani::Arbitrary for Error {
 fn any()->Self {match kani::any::<u8>()%8 {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
}
impl kani::Arbitrary for Variant {
 fn any()->Self {match kani::any::<u8>()%3 {0=>Variant::S1,1=>Variant::S2,_=>Variant::D}}
}

#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control() {let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}
