use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCI_NoteReference.rs"] mod reference;
#[kani::proof]
#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn note_forward(){
 let owner:[u32;8]=kani::any();let salt:[u32;8]=kani::any();
 let value:u32=kani::any();kani::assume(value<P);let asset:u32=kani::any();
 let owner_m=owner.map(M31);let salt_m=salt.map(M31);let reply=([0u32;8]).map(|_|M31(kani::any()));
 let expected=reference::note_input(owner,value,asset,salt);
 let mut calls=0usize;
 let got=note_commitment_with(&owner_m,value,M31(asset),&salt_m,&mut |domain,input:&[M31]|{
  calls+=1;assert_eq!(domain,DOMAIN_NOTE);assert_eq!(input.len(),18);
  assert!((input.iter().zip(expected).all(|(x,y)|x.0==y))!=cfg!(PCI_NEG_NOTE));
  reply
 });
 assert_eq!(calls,1);assert_eq!(got,reply);
}
