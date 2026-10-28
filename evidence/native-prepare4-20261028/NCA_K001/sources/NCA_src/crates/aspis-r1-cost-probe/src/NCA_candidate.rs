use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(6)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_serializer_window(){
 let mut bytes:[u8;32]=kani::any(); let index:usize=kani::any();let k:usize=kani::any();let limb:u32=kani::any();
 kani::assume(index<8&&k<32);let before=bytes[k];
 // One reached native iterator step, retaining the ACTUAL full [u8;32] carrier.
 let mut step=bytes[4*index..].chunks_exact_mut(4).zip(core::iter::once(limb));
 let (chunk,limb)=step.next().unwrap();chunk.copy_from_slice(&limb.to_le_bytes());
 if k>=4*index&&k<4*index+4 {assert_eq!(bytes[k],((limb>>((k-4*index)*8))&255)as u8);}
 else {assert_eq!(bytes[k],before);}
 kani::cover!(index==7&&k==31,"last serializer window and byte reached");
}
#[kani::proof] #[kani::unwind(6)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_serializer_window_wrong(){
 let mut bytes:[u8;32]=kani::any();let index:usize=kani::any();kani::assume(index<8);bytes[4*index]=0;
 let mut step=bytes[4*index..].chunks_exact_mut(4).zip(core::iter::once(1u32));
 let(chunk,limb)=step.next().unwrap();chunk.copy_from_slice(&limb.to_le_bytes());
 assert_eq!(bytes[4*index],0,"negative control: written byte must change");
}
