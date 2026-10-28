use super::*;
#[path="NDF_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(ValidatedRecord::row)]
fn row_contract(){let bytes:[u8;5]=kani::any();let r=ValidatedRecord{row:kani::any(),framed:&bytes};let _=r.row();}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::row)]
fn row_caller(){let bytes:[u8;5]=kani::any();let r=ValidatedRecord{row:kani::any(),framed:&bytes};assert_eq!(r.row(),reference::validated_row_ref(r.row));}
#[kani::proof] #[kani::stub_verified(ValidatedRecord::row)]
fn row_wrong(){let bytes:[u8;5]=kani::any();let r=ValidatedRecord{row:kani::any(),framed:&bytes};assert_ne!(r.row(),reference::validated_row_ref(r.row));}
