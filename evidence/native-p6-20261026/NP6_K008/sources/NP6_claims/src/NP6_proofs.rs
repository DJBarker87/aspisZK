use crate::*;
// Isolated complete Result equality: remove debug formatting and coverage from
// the timed-out K003 goal; all normal memory/bounds/overflow checks remain.
#[kani::proof]
#[kani::unwind(32)]
fn NP6_claims_result_plain() {
 let framed: [u8;2789] = kani::any();
 let root=[0u8;32];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let native=shipped::call(&prefix);
 let owned=reference::call(&prefix);
 assert!(native.is_ok()==owned.is_ok());
 if let (Err(a),Err(b))=(native,owned) {assert!(a==b);}
}
