use super::*;
#[path="NCO_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(row_shape)]
fn shape_contract(){let _=row_shape(kani::any());}
#[kani::proof] #[kani::stub_verified(row_shape)]
fn shape_caller(){let row:u8=kani::any();assert_eq!(row_shape(row),reference::row_shape_ref(row));}
#[kani::proof] #[kani::stub_verified(row_shape)]
fn shape_caller_wrong(){let row:u8=kani::any();assert_ne!(row_shape(row),reference::row_shape_ref(row));}
