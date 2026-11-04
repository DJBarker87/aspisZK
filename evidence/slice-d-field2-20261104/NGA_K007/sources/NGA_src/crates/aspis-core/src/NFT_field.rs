use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
pub(super) fn cm_bytes_matches(v:CM31,b:&[u8])->bool{
 b[0]==v.a.0 as u8 && b[1]==(v.a.0>>8)as u8 && b[2]==(v.a.0>>16)as u8 && b[3]==(v.a.0>>24)as u8 &&
 b[4]==v.b.0 as u8 && b[5]==(v.b.0>>8)as u8 && b[6]==(v.b.0>>16)as u8 && b[7]==(v.b.0>>24)as u8
}
pub(super) fn qm_bytes_matches(v:QM31,b:&[u8])->bool{cm_bytes_matches(v.c0,&b[0..8]) && cm_bytes_matches(v.c1,&b[8..16])}
#[kani::proof_for_contract(CM31::write_le_bytes)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn cm_write(){let v=any_cm();let mut b:[u8;8]=kani::any();v.write_le_bytes(&mut b);}
#[kani::proof_for_contract(QM31::write_le_bytes)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn qm_write(){let v=any_q();let mut b:[u8;16]=kani::any();v.write_le_bytes(&mut b);}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy8_positive(){let a:[u8;8]=kani::any();let mut b:[u8;8]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<8);assert!(b[i]==a[i]);}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy8_negative(){let a:[u8;8]=kani::any();let mut b:[u8;8]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<8);assert!(b[i]!=a[i]);}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy16_positive(){let a:[u8;16]=kani::any();let mut b:[u8;16]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<16);assert!(b[i]==a[i]);}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy16_negative(){let a:[u8;16]=kani::any();let mut b:[u8;16]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<16);assert!(b[i]!=a[i]);}

// K005's whole mutable-slice contract timed out. These are direct, fixed-window
// harnesses on the same frozen writer, with no proof_for_contract instrumentation.
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn cm_word_window(){
 let v=any_cm();let mut out:[u8;8]=kani::any();let at:usize=kani::any();kani::assume(at<8);
 v.write_le_bytes(&mut out);
 let word=if at<4{v.a.0}else{v.b.0};let expected=(word>>((at%4)*8))as u8;
 assert!(out[at]==if cfg!(NFT_invert){expected^1}else{expected});
}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn qm_word_window(){
 let v=any_q();let mut out:[u8;16]=kani::any();let at:usize=kani::any();kani::assume(at<16);
 v.write_le_bytes(&mut out);
 let word=match at/4{0=>v.c0.a.0,1=>v.c0.b.0,2=>v.c1.a.0,_=>v.c1.b.0};let expected=(word>>((at%4)*8))as u8;
 assert!(out[at]==if cfg!(NFT_invert){expected^1}else{expected});
}

#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn cm_frame_window(){
 let v=any_cm();let mut b:[u8;12]=kani::any();let at:usize=kani::any();kani::assume(at<12);
 let old=b[at];v.write_le_bytes(&mut b[2..10]);
 let expected=if at>=2&&at<10{let i=at-2;let w=if i<4{v.a.0}else{v.b.0};(w>>((i%4)*8))as u8}else{old};
 assert!(b[at]==if cfg!(NFT_invert){expected^1}else{expected});
}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn qm_frame_window(){
 let v=any_q();let mut b:[u8;20]=kani::any();let at:usize=kani::any();kani::assume(at<20);
 let old=b[at];v.write_le_bytes(&mut b[2..18]);
 let expected=if at>=2&&at<18{let i=at-2;let w=match i/4{0=>v.c0.a.0,1=>v.c0.b.0,2=>v.c1.a.0,_=>v.c1.b.0};(w>>((i%4)*8))as u8}else{old};
 assert!(b[at]==if cfg!(NFT_invert){expected^1}else{expected});
}
