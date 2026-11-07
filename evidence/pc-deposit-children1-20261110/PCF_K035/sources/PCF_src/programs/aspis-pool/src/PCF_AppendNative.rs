use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(append_roots_unchecked)]
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
#[kani::modifies(data)]
#[kani::ensures(|_| data[0]==7)]
fn shape(data:&mut[u8]){ data[0]=7; data[1]=9; }
#[kani::proof_for_contract(shape)] fn shape_positive(){let mut d:[u8;2]=kani::any();shape(&mut d);}
#[kani::proof] fn shape_real(){let mut d:[u8;2]=kani::any();shape(&mut d);assert_eq!(d[1],9);}
#[kani::proof] #[kani::stub_verified(shape)]
fn shape_stub(){let mut d:[u8;2]=kani::any();shape(&mut d);assert_eq!(d[1],9);}
#[kani::requires(data.len()>=2)] #[kani::modifies(data)] #[kani::ensures(|_| data[0]!=7)]
fn shape_inverse(data:&mut[u8]){data[0]=7;data[1]=9;}
#[kani::proof_for_contract(shape_inverse)]fn shape_inverse_proof(){let mut d:[u8;2]=kani::any();shape_inverse(&mut d);}
#[kani::requires(data.len()>=2)] #[kani::modifies(&mut data[0..1])] #[kani::ensures(|_| data[0]==7)]
fn shape_bad_frame(data:&mut[u8]){data[0]=7;data[1]=9;}
#[kani::proof_for_contract(shape_bad_frame)]fn shape_bad_frame_proof(){let mut d:[u8;2]=kani::any();shape_bad_frame(&mut d);}
#[kani::proof] #[kani::unwind(4)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_inverse(){let src:[u8;2]=kani::any();let mut dst:[u8;2]=kani::any();dst.copy_from_slice(&src);let j:usize=kani::any();kani::assume(j<2);assert_ne!(dst[j],src[j]);}
