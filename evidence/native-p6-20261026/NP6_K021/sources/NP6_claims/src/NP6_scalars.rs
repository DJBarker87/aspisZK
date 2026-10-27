//! Unary scalar projection; complete source body, direct input u32 decoding.
use crate::*;
use aspis_core::field::P;
fn raw(framed:&[u8;3717],at:usize)->u32 {
 u32::from_le_bytes([framed[at],framed[at+1],framed[at+2],framed[at+3]])
}
fn verify<const NATIVE:bool>() {
 let framed:[u8;3717]=kani::any();let root=[0u8;32];
 let chosen=(kani::any::<u8>()as usize)%87;
 let limb=(kani::any::<u8>()as usize)%4;
 let expected=raw(&framed,5+32*chosen+4*limb);
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let got=if NATIVE {shipped::call(&prefix)}else{reference::call(&prefix)};
 assert!(raw(&framed,5+32*chosen+4*limb)==expected);
 if let Ok(out)=got {
  let q=out[chosen/29][chosen%29];
  let actual=match limb {0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0};
  assert!(expected<P);assert!(actual==expected);
 }
}
#[kani::proof] #[kani::unwind(32)] fn NP6_native_scalar_contents(){verify::<true>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_reference_scalar_contents(){verify::<false>();}
