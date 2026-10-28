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
