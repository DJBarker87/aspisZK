use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCI_NoteReference.rs"] mod reference;
static mut EXPECTED:[u32;18]=[0;18];
static mut REPLY:[u32;8]=[0;8];
static mut CALLS:usize=0;
fn hash_reply(domain:M31,input:&[M31])->Digest{
 assert_eq!(domain,DOMAIN_NOTE);assert_eq!(input.len(),18);
 for i in 0..18{assert_eq!(input[i].0,unsafe{EXPECTED[i]});}
 unsafe{CALLS+=1;REPLY.map(M31)}
}
// Generic signature preserved: exact closed273 forwarding law, not a monomorphic wrapper.
fn note_cut<H:FnMut(M31,&[M31])->Digest>(owner:&Digest,value:u32,asset:M31,salt:&Digest,hash:&mut H)->Digest{
 assert!(value<P);
 let words=reference::note_input(owner.map(|x|x.0),value,asset.0,salt.map(|x|x.0));
 let mut fields=words.map(M31);
 #[cfg(PCI_NOTE_CUT_MUTANT)]{fields[0].0^=1;}
 hash(DOMAIN_NOTE,&fields)
}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(note_commitment_with,note_cut)]
#[kani::stub(crate::poseidon2::hash_fields,hash_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn note_caller(){
 let owner:[u32;8]=kani::any();let salt:[u32;8]=kani::any();let value:u32=kani::any();kani::assume(value<P);let asset:u32=kani::any();let reply:[u32;8]=kani::any();
 unsafe{EXPECTED=reference::note_input(owner,value,asset,salt);REPLY=reply;CALLS=0;}
 let mut input=owner.map(M31);
 #[cfg(PCI_NOTE_CALLER_MUTANT)]{input[0].0^=1;}
 #[cfg(not(PCI_NOTE_POOL_WRAPPER))]
 let got=note_commitment(&input,value,M31(asset),&salt.map(M31));
 #[cfg(PCI_NOTE_POOL_WRAPPER)]
 let got=crate::pool_v1::pool_v1_note_commitment(&input,value,M31(asset),&salt.map(M31));
 assert!((got.map(|x|x.0)==reply && unsafe{CALLS}==1)!=cfg!(PCI_NEG_NOTE_CALLER));
}
