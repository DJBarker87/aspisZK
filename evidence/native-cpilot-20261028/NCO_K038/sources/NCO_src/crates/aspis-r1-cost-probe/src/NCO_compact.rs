use super::*;
#[path="NCO_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(compact_row)]
fn compact_row_contract(){let _=compact_row(kani::any());}
#[kani::proof] #[kani::stub_verified(compact_row)]
fn compact_row_caller(){let row:u8=kani::any();assert_eq!(compact_row(row),reference::compact_row_ref(row));}
#[kani::proof] #[kani::stub_verified(compact_row)]
fn compact_row_wrong(){let row:u8=kani::any();assert_ne!(compact_row(row),reference::compact_row_ref(row));}
