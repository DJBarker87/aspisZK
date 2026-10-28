use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn verdict(v:bool)->bool{if cfg!(NDD_negative_verifier){!v}else{v}}
#[kani::proof_for_contract(index_at)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn index_contract(){let x:[u32;16]=kani::any();index_at(&x,kani::any());}
#[kani::proof_for_contract(value_at)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn value_contract(){let x:[[u8;32];16]=kani::any();value_at(&x,kani::any());}
#[kani::proof_for_contract(root_matches)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn root_contract(){let x:[[u8;32];16]=kani::any();let r:[u8;32]=kani::any();root_matches(&x,&r);}
#[cfg(NDD_bits)] #[kani::proof_for_contract(Arity::bits)]
fn bits_contract(){let x=if kani::any(){Arity::Eight}else{Arity::Two};x.bits();}
// Static recorder only. No SHA implementation and no function-pointer observer.
#[derive(Clone,Copy)]
struct Recorder{a:[u8;32],b:[u8;32],reply:[u8;32]}
impl Digest32 for Recorder{
 fn digest(&self,p:&[&[u8]])->[u8;32]{
  assert_eq!(p.len(),3);
  if cfg!(NDD_negative_digest){assert_ne!(p[0],&[BINARY_NODE_TAG]);}
  else{assert_eq!(p[0],&[BINARY_NODE_TAG]);}
  assert_eq!(p[1],&self.a);assert_eq!(p[2],&self.b);
  self.reply
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn occupied_grammar(){let v:[[u8;32];16]=kani::any();let i:usize=kani::any();kani::assume(i<15);let r:[u8;32]=kani::any();let h=Recorder{a:v[i],b:v[i+1],reply:r};assert_eq!(occupied_binary_parent(h,&v,i),r);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sibling_grammar(){let v:[[u8;32];16]=kani::any();let i:usize=kani::any();kani::assume(i<16);let s:[u8;32]=kani::any();let r:[u8;32]=kani::any();let left:bool=kani::any();let h=Recorder{a:if left{v[i]}else{s},b:if left{s}else{v[i]},reply:r};assert_eq!(sibling_binary_parent(h,&v,i,&s,left),r);}
