use super::*;
#[path="PCB_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(root_history_location)]
fn location_contract(){let _=root_history_location(kani::any());}
