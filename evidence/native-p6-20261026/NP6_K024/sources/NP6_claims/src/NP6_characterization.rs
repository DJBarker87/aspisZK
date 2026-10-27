//! Unary whole-source characterization to avoid two full decoder executions.
//! No assumptions, stubs, disabled checks or reduced decoder bodies.
use crate::*;
use aspis_core::field::QM31;
fn verify<const NATIVE:bool>() {
 let framed:[u8;3717]=kani::any();let root=[0u8;32];
 let byte=(kani::any::<u16>()as usize)%3717;let snapshot=framed[byte];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let got=if NATIVE {shipped::call(&prefix)}else{reference::call(&prefix)};
 assert!(framed[byte]==snapshot);
 let chosen=(kani::any::<u8>()as usize)%87;
 let offset=5+32*chosen;
 let value=QM31::from_le_bytes(&framed[offset..offset+16]);
 match got {
  Ok(out)=>{
   assert!(value.is_some());
   if let Some(value)=value {assert!(out[chosen/29][chosen%29]==value);}
  },
  Err(r1_wire::Error::NonCanonical{row,value:bad})=>{
   assert!(row==25);assert!(bad<87);
   if bad<87 {let off=5+32*bad;assert!(QM31::from_le_bytes(&framed[off..off+16]).is_none());}
   if chosen<bad {assert!(value.is_some());}
  },
  Err(_)=>assert!(false),
 }
}
#[kani::proof] #[kani::unwind(32)] fn NP6_native_characterization(){verify::<true>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_reference_characterization(){verify::<false>();}
