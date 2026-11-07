use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Exact deployed enum coverage; feature prover is disabled in deployed receipts.
impl kani::Arbitrary for Error {
 fn any()->Self {match kani::any::<u8>()%8 {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
}
impl kani::Arbitrary for Variant {
 fn any()->Self {match kani::any::<u8>()%3 {0=>Variant::S1,1=>Variant::S2,_=>Variant::D}}
}

pub(super) fn NMD_parse_ref(proof:&[u8])->Result<Variant,Error> {
 if proof.len()!=57607 {return Err(Error::Parse);}
 if proof[0]!=compact::MAGIC[0]||proof[1]!=compact::MAGIC[1]||proof[2]!=compact::MAGIC[2]||proof[3]!=compact::MAGIC[3]||proof[4]!=compact::MAGIC[4]||proof[5]!=compact::MAGIC[5]||proof[6]!=compact::MAGIC[6]||proof[7]!=compact::MAGIC[7]||proof[8]!=2||proof[9]!=0||proof[10]!=0||proof[11]!=0||proof[12]!=0||proof[13]!=0||proof[14]!=0||proof[15]!=0 {Err(Error::Parse)}else{Ok(Variant::S2)}
}
#[kani::proof_for_contract(parse_shape)]#[kani::unwind(9)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_actual_parse_contract(){let bytes:[u8;57607]=kani::any();parse_shape(&bytes);}
#[kani::proof]#[kani::unwind(9)]
#[kani::stub_verified(parse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_actual_parse_caller(){let bytes:[u8;57607]=kani::any();let result=parse_shape(&bytes);assert_eq!(result,NMD_parse_ref(&bytes));}
#[kani::proof]#[kani::unwind(9)]
#[kani::stub_verified(parse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_actual_parse_caller_inverse(){let bytes:[u8;57607]=kani::any();let result=parse_shape(&bytes);assert_ne!(result,NMD_parse_ref(&bytes));}
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control(){let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}

#[kani::proof]#[kani::unwind(9)]
#[kani::stub_verified(parse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_actual_parse_frame(){let bytes:[u8;57607]=kani::any();let i:usize=kani::any();kani::assume(i<57607);let before=bytes[i];let _result=parse_shape(&bytes);assert_eq!(bytes[i],before);}
