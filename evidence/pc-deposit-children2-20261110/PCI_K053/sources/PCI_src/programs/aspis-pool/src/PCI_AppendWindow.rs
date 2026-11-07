use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// (ah) exact loop body, with its mutable range projected to the valid owned window.
fn append_window(data:&mut [u8;32],filled:u16,offset:usize,root:&Digest)->usize{
 let slot=usize::from(filled)+offset;
 let start=PAGE_ROOTS_OFFSET+slot*32;
 data[0..32].copy_from_slice(&encode_digest_canonical(root));
 start
}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn append_window_step(){
 let filled:u16=kani::any();let offset:usize=kani::any();
 kani::assume(filled<=256);kani::assume(offset<256-usize::from(filled));
 let raw:[u32;8]=kani::any();let root=raw.map(aspis_core::field::M31);let before:[u8;32]=kani::any();let mut data=before;
 let start=append_window(&mut data,filled,offset,&root);
 let byte:usize=kani::any();kani::assume(byte<32);
 let expected=(raw[byte/4]>>(8*(byte%4))) as u8;
 assert!((data[byte]==expected)!=cfg!(PCI_NEG_APPEND_WINDOW));
 assert_eq!(start,64+32*(usize::from(filled)+offset));
}
