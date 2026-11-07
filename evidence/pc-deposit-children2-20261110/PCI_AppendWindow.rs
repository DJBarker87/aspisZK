extern crate alloc;
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn encode_spec(root:&Digest)->[u8;32]{
 let mut out=[((root[0].0>>0) as u8),((root[0].0>>8) as u8),((root[0].0>>16) as u8),((root[0].0>>24) as u8),((root[1].0>>0) as u8),((root[1].0>>8) as u8),((root[1].0>>16) as u8),((root[1].0>>24) as u8),((root[2].0>>0) as u8),((root[2].0>>8) as u8),((root[2].0>>16) as u8),((root[2].0>>24) as u8),((root[3].0>>0) as u8),((root[3].0>>8) as u8),((root[3].0>>16) as u8),((root[3].0>>24) as u8),((root[4].0>>0) as u8),((root[4].0>>8) as u8),((root[4].0>>16) as u8),((root[4].0>>24) as u8),((root[5].0>>0) as u8),((root[5].0>>8) as u8),((root[5].0>>16) as u8),((root[5].0>>24) as u8),((root[6].0>>0) as u8),((root[6].0>>8) as u8),((root[6].0>>16) as u8),((root[6].0>>24) as u8),((root[7].0>>0) as u8),((root[7].0>>8) as u8),((root[7].0>>16) as u8),((root[7].0>>24) as u8)];
 #[cfg(PCI_APPEND_SPEC_MUTANT)]{out[0]^=1;}
 out
}
// (ah) exact loop body, with its mutable range projected to the valid owned window.
fn append_window(data:&mut [u8;32],filled:u16,offset:usize,root:&Digest)->usize{
 let slot=usize::from(filled)+offset;
 let start=PAGE_ROOTS_OFFSET+slot*32;
 data[0..32].copy_from_slice(&encode_digest_canonical(root));
 start
}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(aspis_statement::encode_digest_canonical,encode_spec)]
fn append_window_step(){
 let filled:u16=kani::any();let offset:usize=kani::any();
 kani::assume(filled<=256);kani::assume(offset<256-usize::from(filled));
 let raw:[u32;8]=kani::any();let mut root=raw.map(aspis_core::field::M31);
 #[cfg(PCI_APPEND_ARG_MUTANT)]{root[0].0^=1;}let before:[u8;32]=kani::any();let mut data=before;
 let start=append_window(&mut data,filled,offset,&root);
 let byte:usize=kani::any();kani::assume(byte<32);
 let expected=(raw[byte/4]>>(8*(byte%4))) as u8;
 assert!((data[byte]==expected)!=cfg!(PCI_NEG_APPEND_WINDOW));
 assert_eq!(start,64+32*(usize::from(filled)+offset));
}
