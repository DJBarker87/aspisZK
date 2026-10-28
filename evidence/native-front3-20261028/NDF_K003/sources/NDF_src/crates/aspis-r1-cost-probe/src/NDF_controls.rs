#[kani::ensures(|r| *r==x)] fn scalar(x:u64)->u64{x}
#[kani::ensures(|r| *r!=x)] fn inverted(x:u64)->u64{x}
#[kani::ensures(|r| *r<=u64::MAX)] fn weak(x:u64)->u64{x}
#[kani::modifies(&mut x[0])] fn badframe(x:&mut [u64;2])->u64{x[1]=1;0}
#[kani::proof_for_contract(scalar)] fn scalar_proof(){let _=scalar(kani::any());}
#[kani::proof_for_contract(inverted)] fn scalar_inverted(){let _=inverted(kani::any());}
#[kani::proof_for_contract(weak)] fn scalar_weak(){let _=weak(kani::any());}
#[kani::proof] fn scalar_real(){let x:u64=kani::any();assert_eq!(weak(x),x);}
#[kani::proof] #[kani::stub_verified(weak)] fn scalar_unimplied(){let x:u64=kani::any();assert_eq!(weak(x),x);}
#[kani::proof_for_contract(badframe)] fn scalar_frame(){let mut x:[u64;2]=kani::any();let _=badframe(&mut x);}
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let a:[u8;32]=kani::any();let mut b:[u8;32]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<32);assert_eq!(b[i],a[i]);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let a:[u8;32]=kani::any();let mut b:[u8;32]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<32);assert_ne!(b[i],a[i]);}
