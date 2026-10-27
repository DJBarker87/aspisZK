//! Whole-source first-error characterization, split into witness and prefix.
use crate::*;
use aspis_core::field::P;
fn raw(framed:&[u8;3717],at:usize)->u32 {
 u32::from_le_bytes([framed[at],framed[at+1],framed[at+2],framed[at+3]])
}
fn verify<const NATIVE:bool,const PRIOR:bool>() {
 let framed:[u8;3717]=kani::any();let root=[0u8;32];
 let chosen=(kani::any::<u8>()as usize)%87;
 let limb=(kani::any::<u8>()as usize)%4;
 let before=raw(&framed,5+32*chosen+4*limb);
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let got=if NATIVE {shipped::call(&prefix)}else{reference::call(&prefix)};
 if let Err(error)=got {
  match error {
   r1_wire::Error::NonCanonical{row,value:bad}=>{
    if PRIOR {if chosen<bad {assert!(before<P);}}
    else {
     assert!(row==25);assert!(bad<87);
     if bad<87 {let off=5+32*bad;
      assert!(raw(&framed,off)>=P||raw(&framed,off+4)>=P||raw(&framed,off+8)>=P||raw(&framed,off+12)>=P);
     }
    }
   },
   _=>{if !PRIOR {assert!(false);}},
  }
 }
}
#[kani::proof] #[kani::unwind(32)] fn NP6_native_bad_witness(){verify::<true,false>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_native_valid_prefix(){verify::<true,true>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_reference_bad_witness(){verify::<false,false>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_reference_valid_prefix(){verify::<false,true>();}
