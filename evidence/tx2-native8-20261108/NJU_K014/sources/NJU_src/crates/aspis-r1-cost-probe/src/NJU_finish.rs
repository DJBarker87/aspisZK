//! Arbitrary one-field windows at the actual frozen weights::field call.
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(bytes:&[u8;32])->[u32;8]{core::array::from_fn(|j|u32::from_le_bytes([bytes[4*j],bytes[4*j+1],bytes[4*j+2],bytes[4*j+3]]))}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn decode_total(){
 let bytes:[u8;32]=kani::any();let ws=words(&bytes);let index:usize=kani::any();kani::assume(index<8);
 let expected=ws.iter().all(|&x|x<0x7fffffff);
 let out=E::from_le_bytes(&bytes);
 if cfg!(NJU_invert){assert_eq!(out.is_some(),!expected);}else{assert_eq!(out.is_some(),expected);}
 if let Some(x)=out{assert_eq!(x.to_limbs()[index],ws[index]);}
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn field_canonical(){
 let bytes:[u8;32]=kani::any();let ws=words(&bytes);for x in ws{kani::assume(x<0x7fffffff);}
 let j:usize=kani::any();kani::assume(j<8);
 let out=super::field(&bytes,0);
 let expected=ws[j]^(if cfg!(NJU_invert){1}else{0});assert_eq!(out.to_limbs()[j],expected);
}
#[kani::proof]
#[kani::should_panic]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn field_noncanonical(){
 let mut bytes:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<8);
 let ws=words(&bytes);kani::assume(ws[j]>=0x7fffffff);
 if cfg!(NJU_invert){bytes=[0;32];}
 let _=super::field(&bytes,0);
}
#[kani::proof]
#[kani::should_panic]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn field_short(){
 let bytes:[u8;32]=[0;32];let n:usize=kani::any();kani::assume(n<32);
 let slice=if cfg!(NJU_invert){&bytes[..]}else{&bytes[..n]};let _=super::field(slice,0);
}

// Universal no-return properties are inspected separately from the expected
// panic property. should_panic alone is only existential and earns no credit.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn noncanonical_no_return(){
 let mut bytes:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<8);
 let ws=words(&bytes);kani::assume(ws[j]>=0x7fffffff);
 if cfg!(NJU_invert){bytes=[0;32];}
 let _=super::field(&bytes,0);
 assert!(false,"NJU_NONCANONICAL_RETURNED");
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn short_no_return(){
 let bytes:[u8;32]=[0;32];let n:usize=kani::any();kani::assume(n<32);
 let slice=if cfg!(NJU_invert){&bytes[..]}else{&bytes[..n]};let _=super::field(slice,0);
 assert!(false,"NJU_SHORT_RETURNED");
}
