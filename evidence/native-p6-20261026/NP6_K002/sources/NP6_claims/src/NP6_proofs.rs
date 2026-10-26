use crate::*;
#[kani::proof]
#[kani::unwind(32)]
fn NP6_claims_selected_slot() {
 let framed: [u8;2789] = kani::any();
 let root=[0u8;32];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let native=shipped::call(&prefix);
 let owned=reference::call(&prefix);
 match (native,owned) {
  (Ok(a),Ok(b))=>{
   let i=(kani::any::<u8>()%3) as usize;
   let j=(kani::any::<u8>()%29) as usize;
   assert_eq!(a[i][j],b[i][j]);
   kani::cover!(true,"complete native box with arbitrary selected slot");
  },
  (Err(a),Err(b))=>{assert_eq!(a,b);kani::cover!(true,"exact decoder rejection");},
  _=>panic!("Result mismatch"),
 }
}
