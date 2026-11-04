use aspis_core::field::{M31,CM31,QM31};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub fn NGO_decode_le(bytes:&[u8])->Option<QM31>{
 assert_eq!(bytes.len(),16);
 fn word(b:&[u8],i:usize)->u32{u32::from(b[i])|(u32::from(b[i+1])<<8u32)|(u32::from(b[i+2])<<16u32)|(u32::from(b[i+3])<<24u32)}
 let a=word(bytes,0);let b=word(bytes,4);let c=word(bytes,8);let d=word(bytes,12);
 if a>=0x7fffffff||b>=0x7fffffff||c>=0x7fffffff||d>=0x7fffffff{return None;}
 Some(QM31{c0:CM31{a:M31(a),b:M31(b)},c1:CM31{a:M31(c),b:M31(d)}})
}

#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NGO_q_association() {
 let bytes:[u8;16]=kani::any();
 let actual=QM31::from_le_bytes(&bytes);
 let reference=NGO_decode_le(&bytes);
 #[cfg(not(NGO_invert))] assert_eq!(actual,reference);
 #[cfg(NGO_invert)] assert_ne!(actual,reference);
 #[cfg(NGO_copy_corrupt)] {let mut other=bytes;other[0]^=1;assert_eq!(actual,NGO_decode_le(&other));}
}

fn NGD_decode_le(bytes:&[u8])->Option<QM31>{
 assert_eq!(bytes.len(),16);
 fn word(b:&[u8],i:usize)->u32{u32::from(b[i])|(u32::from(b[i+1])<<8)|(u32::from(b[i+2])<<16)|(u32::from(b[i+3])<<24)}
 let a=word(bytes,0);let b=word(bytes,4);let c=word(bytes,8);let d=word(bytes,12);
 if a>=0x7fffffff||b>=0x7fffffff||c>=0x7fffffff||d>=0x7fffffff{return None;}
 Some(QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(a),b:aspis_core::field::M31(b)},c1:aspis_core::field::CM31{a:aspis_core::field::M31(c),b:aspis_core::field::M31(d)}})
}
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NGO_retained_stub_association() {
 let bytes:[u8;16]=kani::any();
 let retained=NGD_decode_le(&bytes);
 let reference=NGO_decode_le(&bytes);
 #[cfg(not(NGO_invert))] assert_eq!(retained,reference);
 #[cfg(NGO_invert)] assert_ne!(retained,reference);
}

#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NGO_initial_28() {
 let i:usize=kani::any();kani::assume(i<28);
 let out = [QM31::ZERO; 28];
 let q=out[i];
 #[cfg(not(NGO_invert))] assert!(q.c0.a.0==0 && q.c0.b.0==0 && q.c1.a.0==0 && q.c1.b.0==0);
 #[cfg(NGO_invert)] assert!(q.c0.a.0==1);
}

#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NGO_initial_29() {
 let i:usize=kani::any();kani::assume(i<29);
 let out = [QM31::ZERO; 29];
 let q=out[i];
 #[cfg(not(NGO_invert))] assert!(q.c0.a.0==0 && q.c0.b.0==0 && q.c1.a.0==0 && q.c1.b.0==0);
 #[cfg(NGO_invert)] assert!(q.c0.a.0==1);
}
