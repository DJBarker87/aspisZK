use crate::*;
use aspis_core::field::P;
// Success-domain source comparison. Every canonical low limb is represented
// by arbitrary u32 % P; no Kani assumption or stub is used. This does not cover
// noncanonical decoder errors and is not the unrestricted P6 gate.
#[kani::proof]
#[kani::unwind(90)]
fn NP6_claims_canonical_contents() {
 let mut framed=[0u8;3717];
 for v in 0..87 {
  for l in 0..4 {
   let word=kani::any::<u32>()%P;
   let bytes=word.to_le_bytes();
   for b in 0..4 {framed[5+v*32+l*4+b]=bytes[b];}
  }
 }
 let root=[0u8;32];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let a=shipped::call(&prefix);
 let b=reference::call(&prefix);
 assert!(a.is_ok());assert!(b.is_ok());
 if let (Ok(a),Ok(b))=(a,b) {
  let i=(kani::any::<u8>()%3) as usize;let j=(kani::any::<u8>()%29) as usize;
  assert!(a[i][j]==b[i][j]);
 }
}
