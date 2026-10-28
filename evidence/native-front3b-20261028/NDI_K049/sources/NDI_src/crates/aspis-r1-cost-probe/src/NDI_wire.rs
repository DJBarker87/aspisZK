use super::*;
#[path="NDI_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(ValidatedRecord::row)]
fn row_contract(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};let _=r.row();}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::row)]
fn row_caller(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};assert_eq!(r.row(),reference::validated_row_ref(r.row));}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::row)]
fn row_wrong(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};assert_ne!(r.row(),reference::validated_row_ref(r.row));}

pub(super) static mut VALUE_REPLY:*const [u8;32]=core::ptr::null();
pub(super) static mut VALUE_ADVANCED:*const [u8;32]=core::ptr::null();
pub(super) static mut VALUE_COORD:usize=0;
pub(super) fn new_matches<H:aspis_core::Digest32>(out:&Result<SemanticTranscript<H>,Error>)->bool {
 unsafe {match out {Ok(t)=>{let p=reference::transcript_new_byte_borrow_ref(&*VALUE_REPLY,VALUE_COORD);(t.state[VALUE_COORD],t.next_row)==(p.0,p.1)},Err(_)=>false}}
}
pub(super) fn sample_matches(out:&Result<[u8;32],Error>,state:&[u8;32],next:u8,row:u8,before:u8,old_next:u8)->bool {
 unsafe {
  if row==old_next {match out {Ok(block)=>{let p=reference::transcript_sample_byte_borrow_ref(&*VALUE_REPLY,&*VALUE_ADVANCED,row,VALUE_COORD);(block[VALUE_COORD],state[VALUE_COORD],next)==(p.0,p.1,p.2)},Err(_)=>false}}
  else {matches!(out,Err(Error::RowOrder{expected,actual}) if *expected==old_next && *actual==row) && state[VALUE_COORD]==before && next==old_next}
 }
}
