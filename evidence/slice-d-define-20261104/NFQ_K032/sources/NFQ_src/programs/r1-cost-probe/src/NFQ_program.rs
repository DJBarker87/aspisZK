use super::*;
#[path="NFQ_scan_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(readonly_buffer_meta_ok)]
fn readonly_contract(){let _=readonly_buffer_meta_ok(kani::any(),kani::any(),kani::any());}
