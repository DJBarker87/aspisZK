use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn bytes(root:&Digest)->[u8;32]{
 let w0=root[0].0.to_le_bytes();
 let w1=root[1].0.to_le_bytes();
 let w2=root[2].0.to_le_bytes();
 let w3=root[3].0.to_le_bytes();
 let w4=root[4].0.to_le_bytes();
 let w5=root[5].0.to_le_bytes();
 let w6=root[6].0.to_le_bytes();
 let w7=root[7].0.to_le_bytes();
 [w0[0],w0[1],w0[2],w0[3],w1[0],w1[1],w1[2],w1[3],w2[0],w2[1],w2[2],w2[3],w3[0],w3[1],w3[2],w3[3],w4[0],w4[1],w4[2],w4[3],w5[0],w5[1],w5[2],w5[3],w6[0],w6[1],w6[2],w6[3],w7[0],w7[1],w7[2],w7[3]]
}
#[kani::proof_for_contract(append_roots_unchecked)]
#[kani::stub(encode_digest_canonical,bytes)]
#[kani::unwind(4)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn empty(){
 let mut data:[u8;58]=kani::any();
 let h=RootPageHeaderV1{pool:Pubkey::new_from_array(kani::any()),page_number:kani::any(),first_sequence:kani::any(),filled:kani::any()};
 kani::assume(h.filled<=256);
 append_roots_unchecked(&mut data,h,&[]);
}
#[kani::requires(data.len()>=2)]
#[kani::modifies(data.first_chunk_mut::<2>().unwrap())]
#[kani::ensures(|_| data[0]==(if flag {7}else{8}))]
fn shape(data:&mut[u8],flag:bool){ data[0]=if flag {7}else{8}; data[1]=if flag {9}else{10}; }
#[kani::proof_for_contract(shape)] fn shape_positive(){let mut d:[u8;2]=kani::any();shape(&mut d,kani::any());}
#[kani::proof] fn shape_real(){let mut d:[u8;2]=kani::any();let flag:bool=kani::any();shape(&mut d,flag);assert_eq!(d[1],if flag {9}else{10});}
#[kani::proof] #[kani::stub_verified(shape)]
fn shape_stub(){let mut d:[u8;2]=kani::any();let flag:bool=kani::any();shape(&mut d,flag);assert_eq!(d[1],if flag {9}else{10});}
#[kani::requires(data.len()>=2)] #[kani::modifies(data.first_chunk_mut::<2>().unwrap())] #[kani::ensures(|_| data[0]!=(if flag {7}else{8}))]
fn shape_inverse(data:&mut[u8],flag:bool){data[0]=if flag {7}else{8};data[1]=if flag {9}else{10};}
#[kani::proof_for_contract(shape_inverse)]fn shape_inverse_proof(){let mut d:[u8;2]=kani::any();shape_inverse(&mut d,kani::any());}
#[kani::requires(data.len()>=2)] #[kani::modifies(data.first_chunk_mut::<1>().unwrap())] #[kani::ensures(|_| data[0]==(if flag {7}else{8}))]
fn shape_bad_frame(data:&mut[u8],flag:bool){data[0]=if flag {7}else{8};data[1]=if flag {9}else{10};}
#[kani::proof_for_contract(shape_bad_frame)]fn shape_bad_frame_proof(){let mut d:[u8;2]=kani::any();shape_bad_frame(&mut d,kani::any());}
#[kani::proof] #[kani::unwind(4)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_inverse(){let src:[u8;2]=kani::any();let mut dst:[u8;2]=kani::any();dst.copy_from_slice(&src);let j:usize=kani::any();kani::assume(j<2);assert_ne!(dst[j],src[j]);}
