use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::requires(i<3 && j<3)]
#[kani::ensures(|r| (*r == sums) != cfg!(NGH_invert))]
fn shape_identity(sums:[[u64;3];3],i:usize,j:usize)->[[u64;3];3]{sums}
#[kani::proof_for_contract(shape_identity)]
#[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_contract(){shape_identity(kani::any(),kani::any(),kani::any());}
#[kani::requires(true)]
#[kani::ensures(|r| r[0][0] == 0)]
fn weak_shape()->[[u64;3];3]{[[0;3];3]}
#[kani::proof]
#[kani::stub_verified(weak_shape)]
fn shape_unimplied(){assert!(weak_shape()[2][2]==0);}
#[kani::proof]
fn shape_real(){assert!(weak_shape()[2][2]==0);}
#[kani::modifies(ptr)]
#[kani::ensures(|_| true)]
fn shape_bad_frame(ptr:&mut [[u64;3];3],other:&mut u64){ptr[0][0]=0;*other=7;}
#[kani::proof_for_contract(shape_bad_frame)]
fn shape_frame(){let mut a=kani::any();let mut other=kani::any();shape_bad_frame(&mut a,&mut other);}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let src:[[u64;3];3]=kani::any();let mut dst:[[u64;3];3]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]==dst[i][j]);}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let src:[[u64;3];3]=kani::any();let mut dst:[[u64;3];3]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]!=dst[i][j]);}
