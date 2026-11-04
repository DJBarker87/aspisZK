use super::*;
#[path="NFQ_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(row_shape)]
fn shape_contract(){let _=row_shape(kani::any());}
