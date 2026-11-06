use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(bytes:&[u8],at:usize)->u32{u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
fn kw(q:K)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn raw<const N:usize>(){
 let bytes:[u8;32]=kani::any();let at=0usize;
 let mut r=Reader{bytes:&bytes,at};let out=r.raw::<N>();
 let mut i=0;while i<N{assert_eq!(out[i],bytes[at+i]^(if cfg!(NJC_invert){1}else{0}));i+=1;}
 assert_eq!(r.at,at+N);assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),32);
}
fn read_k(){
 let bytes:[u8;16]=kani::any();let at=0usize;
 let expected=[word(&bytes,at),word(&bytes,at+4),word(&bytes,at+8),word(&bytes,at+12)];
 let good=expected[0]<2147483647&&expected[1]<2147483647&&expected[2]<2147483647&&expected[3]<2147483647;
 let mut r=Reader{bytes:&bytes,at};let result=r.k();
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok(q)=>assert_eq!(kw(q),expected),Err(e)=>assert_eq!(e,Error::Checkpoint)}
 assert_eq!(r.at,at+16);assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),16);
}
fn read_e(){
 let bytes:[u8;32]=kani::any();let at=0usize;
 let expected=[word(&bytes,at),word(&bytes,at+4),word(&bytes,at+8),word(&bytes,at+12),word(&bytes,at+16),word(&bytes,at+20),word(&bytes,at+24),word(&bytes,at+28)];
 let good=expected[0]<2147483647&&expected[1]<2147483647&&expected[2]<2147483647&&expected[3]<2147483647&&expected[4]<2147483647&&expected[5]<2147483647&&expected[6]<2147483647&&expected[7]<2147483647;
 let mut r=Reader{bytes:&bytes,at};let result=r.e();
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok(q)=>assert_eq!(q.to_limbs(),expected),Err(e)=>assert_eq!(e,Error::Checkpoint)}
 assert_eq!(r.at,at+32);assert_eq!(r.bytes.as_ptr(),bytes.as_ptr());assert_eq!(r.bytes.len(),32);
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw4(){raw::<4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw4_renamed(){raw::<4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw16(){raw::<16>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw16_renamed(){raw::<16>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw32(){raw::<32>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn raw32_renamed(){raw::<32>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn k(){read_k();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn k_renamed(){read_k();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn e(){read_e();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn e_renamed(){read_e();}
