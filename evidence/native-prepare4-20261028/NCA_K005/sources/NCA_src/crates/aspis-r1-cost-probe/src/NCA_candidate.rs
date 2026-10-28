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

#[kani::proof] #[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_serializer_zip_step(){
 let mut bytes:[u8;32]=kani::any();let limbs:[u32;8]=kani::any();let index:usize=kani::any();let k:usize=kani::any();
 kani::assume(index<8&&k<32);
 kani::assume(limbs[0]<aspis_core::field::P);
 kani::assume(limbs[1]<aspis_core::field::P);
 kani::assume(limbs[2]<aspis_core::field::P);
 kani::assume(limbs[3]<aspis_core::field::P);
 kani::assume(limbs[4]<aspis_core::field::P);
 kani::assume(limbs[5]<aspis_core::field::P);
 kani::assume(limbs[6]<aspis_core::field::P);
 kani::assume(limbs[7]<aspis_core::field::P);
 let x=E::from_limbs(limbs).unwrap();let before=bytes[k];
 // nth advances only the iterator; exactly ONE body write, on arbitrary full carrier.
 let (chunk,limb)=bytes.chunks_exact_mut(4).zip(x.to_limbs()).nth(index).unwrap();
 chunk.copy_from_slice(&limb.to_le_bytes());
 assert_eq!(limb,limbs[index]);
 if k>=4*index&&k<4*index+4 {assert_eq!(bytes[k],((limbs[index]>>((k-4*index)*8))&255)as u8);}
 else {assert_eq!(bytes[k],before);}
 kani::cover!(index==7&&k==31,"actual zip last limb window");
}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_serializer_zip_wrong(){
 let mut bytes:[u8;32]=kani::any();let index:usize=kani::any();kani::assume(index<8);bytes[4*index]=0;
 let x=E::from_limbs([1;8]).unwrap();
 let(chunk,limb)=bytes.chunks_exact_mut(4).zip(x.to_limbs()).nth(index).unwrap();
 chunk.copy_from_slice(&limb.to_le_bytes());assert_eq!(bytes[4*index],0,"negative actual zip control");
}
