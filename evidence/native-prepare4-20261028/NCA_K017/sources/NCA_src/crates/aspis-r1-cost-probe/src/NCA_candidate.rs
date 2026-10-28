use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn NCA_root_copy(input:&[u8],out:&mut[u8]){out[..32].copy_from_slice(&input[..32]);}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_root_full_value(){
 let input:[u8;7015]=kani::any();let mut logical:[u8;14759]=kani::any();let j:usize=kani::any();kani::assume(j<32);
 NCA_root_copy(&input,&mut logical[..13831]);assert_eq!(logical[j],input[j]);
 kani::cover!(j==31,"last root byte in SAME full logical carrier");
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_root_full_frame(){
 let input:[u8;7015]=kani::any();let mut logical:[u8;14759]=kani::any();let j:usize=kani::any();kani::assume(j>=32&&j<14759);let old=logical[j];
 NCA_root_copy(&input,&mut logical[..13831]);assert_eq!(logical[j],old);
 kani::cover!(j==14758,"last y1 exterior byte in SAME full logical carrier");
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_root_full_wrong(){
 let mut input:[u8;7015]=kani::any();let mut logical:[u8;14759]=kani::any();input[31]=1;logical[31]=0;
 NCA_root_copy(&input,&mut logical[..13831]);assert_eq!(logical[31],0,"negative root last byte");
}

#[repr(C)]struct NCA_RootCarrier{root:[u8;32],semantic_tail:[u8;13799],y1:[u8;928]}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_root_product_frame(){
 let input:[u8;7015]=kani::any();let mut out=NCA_RootCarrier{root:kani::any(),semantic_tail:kani::any(),y1:kani::any()};
 let k:usize=kani::any();let y:usize=kani::any();kani::assume(k<13799&&y<928);let old_sem=out.semantic_tail[k];let old_y=out.y1[y];
 assert_eq!(core::mem::size_of::<NCA_RootCarrier>(),14759);assert_eq!(core::mem::align_of::<NCA_RootCarrier>(),1);
 let full=unsafe{core::slice::from_raw_parts_mut((&mut out as *mut NCA_RootCarrier).cast::<u8>(),14759)};
 NCA_root_copy(&input,&mut full[..13831]);assert_eq!(out.semantic_tail[k],old_sem);assert_eq!(out.y1[y],old_y);
 kani::cover!(k==13798&&y==927,"both full exterior endpoints");
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_root_product_wrong(){
 let mut input:[u8;7015]=kani::any();let mut out=NCA_RootCarrier{root:kani::any(),semantic_tail:kani::any(),y1:kani::any()};input[31]=1;out.root[31]=0;
 let full=unsafe{core::slice::from_raw_parts_mut((&mut out as *mut NCA_RootCarrier).cast::<u8>(),14759)};NCA_root_copy(&input,&mut full[..13831]);assert_eq!(out.root[31],0,"negative product carrier root");
}
