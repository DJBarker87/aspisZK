use super::*;
extern crate alloc;
use aspis_core::field::M31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCI_DepositReference.rs"]mod reference;
include!("PCI_DepositFission.rs");
fn decode_spec(b:&[u8;32])->Result<aspis_statement::Digest,aspis_statement::AtomicStatementError>{
 let expected=[u32::from_le_bytes([b[0],b[1],b[2],b[3]]),u32::from_le_bytes([b[4],b[5],b[6],b[7]]),u32::from_le_bytes([b[8],b[9],b[10],b[11]]),u32::from_le_bytes([b[12],b[13],b[14],b[15]]),u32::from_le_bytes([b[16],b[17],b[18],b[19]]),u32::from_le_bytes([b[20],b[21],b[22],b[23]]),u32::from_le_bytes([b[24],b[25],b[26],b[27]]),u32::from_le_bytes([b[28],b[29],b[30],b[31]])];
 let ok:bool=kani::any();kani::assume(ok==(reference::canonical(expected)!=cfg!(PCI_DEPOSIT_SPEC_MUTANT)));
 if !ok{return Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)}
 let mut raw=[0u32;8];
 raw[0]=kani::any();kani::assume(raw[0]==expected[0]);
 raw[1]=kani::any();kani::assume(raw[1]==expected[1]);
 raw[2]=kani::any();kani::assume(raw[2]==expected[2]);
 raw[3]=kani::any();kani::assume(raw[3]==expected[3]);
 raw[4]=kani::any();kani::assume(raw[4]==expected[4]);
 raw[5]=kani::any();kani::assume(raw[5]==expected[5]);
 raw[6]=kani::any();kani::assume(raw[6]==expected[6]);
 #[cfg(not(PCI_DEPOSIT_OMIT_OWNER))]
 {raw[7]=kani::any();kani::assume(raw[7]==expected[7]);}
 Ok([M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7])])
}
fn error_tag(e:DepositInstructionFormatErrorV1)->u8{
 use DepositInstructionFormatErrorV1::*;
 match e{WrongLength=>1,WrongMagic=>2,WrongVersion=>3,NonZeroReserved=>4,InvalidAmount=>5,InvalidPayloadLength=>6,NonCanonicalDigest=>7}
}
#[kani::proof] #[kani::unwind(650)]
#[kani::stub(aspis_statement::decode_digest_canonical,decode_spec)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn decode_all(){
 let bytes:[u8;592]=kani::any();let logical_len:usize=kani::any();let magic:[u8;4]=kani::any();
 let i:usize=kani::any();kani::assume(i<592);let before=bytes[i];
 let header:&[u8;80]=(&bytes[..80]).try_into().unwrap();
 let want=reference::decode_reference(header,logical_len,magic);
 let got=decode_fission(&bytes,logical_len,magic);
 let same=match got{
  Err(e)=>want.tag==error_tag(e),
  Ok(r)=>{want.tag==0&&r.owner_key.map(|x|x.0)==want.owner&&r.amount==want.amount&&r.salt.map(|x|x.0)==want.salt&&r.encrypted_note_payload.len()==want.payload_len&&core::ptr::eq(r.encrypted_note_payload,&bytes[80..logical_len])}
 };
 assert!(same!=cfg!(PCI_NEG_DEPOSIT));assert_eq!(bytes[i],before);
}
