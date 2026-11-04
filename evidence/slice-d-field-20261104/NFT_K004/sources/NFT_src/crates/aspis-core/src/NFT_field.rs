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
