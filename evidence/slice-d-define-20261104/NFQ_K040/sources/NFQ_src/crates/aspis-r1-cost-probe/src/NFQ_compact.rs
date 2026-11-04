use super::*;
#[path="NFQ_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(compact_row)]
fn compact_contract(){let _=compact_row(kani::any());}
