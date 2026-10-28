use super::*;
#[path="NDF_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(ValidatedRecord::row)]
fn row_contract(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};let _=r.row();}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::row)]
fn row_caller(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};assert_eq!(r.row(),reference::validated_row_ref(r.row));}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::row)]
fn row_wrong(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};assert_ne!(r.row(),reference::validated_row_ref(r.row));}

#[derive(Clone,Copy)] struct NDF_NoDigest;
impl aspis_core::digest::Digest32 for NDF_NoDigest {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("getter must not call digest")}}
#[kani::proof_for_contract(SemanticTranscript::<NDF_NoDigest>::state)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_contract(){let r=SemanticTranscript{state:kani::any(),next_row:kani::any(),hash:NDF_NoDigest};let _=r.state();}
#[kani::proof] #[kani::stub_verified(SemanticTranscript::<NDF_NoDigest>::state)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_caller(){let r=SemanticTranscript{state:kani::any(),next_row:kani::any(),hash:NDF_NoDigest};assert_eq!(r.state(),reference::state_ref(r.state));}
#[kani::proof] #[kani::stub_verified(SemanticTranscript::<NDF_NoDigest>::state)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_wrong(){let r=SemanticTranscript{state:kani::any(),next_row:kani::any(),hash:NDF_NoDigest};assert_ne!(r.state(),reference::state_ref(r.state));}

#[kani::proof_for_contract(ValidatedRecord::framed)]
fn framed_contract(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};let _=r.framed();}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::framed)]
fn framed_caller(){let bytes:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let r=ValidatedRecord{row:kani::any(),framed:&bytes[..n]};assert_eq!(r.framed(),r.framed);}
