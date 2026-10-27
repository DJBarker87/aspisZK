use crate::*;
#[kani::proof]
#[kani::unwind(120)]
fn NP6_claims_full_arbitrary_contents() {
 let framed: [u8;2789] = kani::any();
 let root=[0u8;32];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let native=shipped::call(&prefix);
 let owned=reference::call(&prefix);
 assert_eq!(native,owned);
 kani::cover!(native.is_ok(),"all three rows decoded and native Box initialized");
 kani::cover!(native.is_err(),"same actual decoding error");
}
