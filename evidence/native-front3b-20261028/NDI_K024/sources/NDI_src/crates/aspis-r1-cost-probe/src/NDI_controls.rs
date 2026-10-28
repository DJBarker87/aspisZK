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

#[kani::ensures(|r| *r==x)] fn array(x:[u8;32])->[u8;32]{x}
#[kani::ensures(|r| *r!=x)] fn array_invert(x:[u8;32])->[u8;32]{x}
#[kani::ensures(|r| r.len()==32)] fn array_weak(x:[u8;32])->[u8;32]{x}
#[kani::modifies(&mut x[0])] fn array_badframe(x:&mut [u8;2])->[u8;32]{x[1]=1;[0;32]}
#[kani::proof_for_contract(array)] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_proof(){let _=array(kani::any());}
#[kani::proof_for_contract(array_invert)] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_inverted(){let _=array_invert(kani::any());}
#[kani::proof_for_contract(array_weak)] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_weak_proof(){let _=array_weak(kani::any());}
#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_real(){let x:[u8;32]=kani::any();assert_eq!(array_weak(x),x);}
#[kani::proof] #[kani::stub_verified(array_weak)] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_unimplied(){let x:[u8;32]=kani::any();assert_eq!(array_weak(x),x);}
#[kani::proof_for_contract(array_badframe)] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_frame(){let mut x:[u8;2]=kani::any();let _=array_badframe(&mut x);}
