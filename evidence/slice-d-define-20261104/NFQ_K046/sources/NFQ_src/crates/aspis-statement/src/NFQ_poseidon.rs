use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn limbs_ref(v:QM31)->[u32;4]{[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]}
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
#[kani::proof_for_contract(extension_limbs)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]

fn limbs_contract(){let _=extension_limbs(any_q());}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]

fn copy_positive(){let src:[u32;4]=kani::any();let mut dst:[u32;4]=kani::any();let k:usize=kani::any();kani::assume(k<4);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[k]==dst[k]);}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]

fn copy_negative(){let src:[u32;4]=kani::any();let mut dst:[u32;4]=kani::any();let k:usize=kani::any();kani::assume(k<4);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[k]!=dst[k]);}
#[kani::modifies()] #[kani::ensures(|r| r[0]==0)]
fn weak_array()->[u32;4]{[0,1,2,3]}
#[kani::proof_for_contract(weak_array)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]

fn array_real(){assert!(weak_array()[1]==1);}
#[kani::proof] #[kani::stub_verified(weak_array)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]

fn array_unimplied(){assert!(weak_array()[1]==1);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r[0]==0)]
fn bad_array_frame(x:&mut[u8;2])->[u32;4]{x[1]=x[1].wrapping_add(1);[0,1,2,3]}
#[kani::proof_for_contract(bad_array_frame)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]

fn array_frame(){let mut x:[u8;2]=kani::any();let _=bad_array_frame(&mut x);}
