// Scratch only: interface fidelity probes, not native implementation credit.
use alloc::vec::Vec;
#[kani::ensures(|r| *r == Ok(x & 1))]
fn result_record(x:u8)->Result<u8,u8>{Ok(x & 1)}
#[kani::ensures(|r| *r != Ok(x & 1))]
fn result_invert(x:u8)->Result<u8,u8>{Ok(x & 1)}
#[kani::proof_for_contract(result_record)]
fn result_positive(){result_record(kani::any());}
#[kani::proof_for_contract(result_invert)]
fn result_negative(){result_invert(kani::any());}
#[kani::ensures(|r| r.is_ok())]
fn result_weak(x:u8)->Result<u8,u8>{Ok(x)}
#[kani::proof_for_contract(result_weak)]
fn result_weak_proof(){result_weak(kani::any());}
#[kani::proof]
fn result_real(){let x:u8=kani::any();assert_eq!(result_weak(x),Ok(x));}
#[kani::proof] #[kani::stub_verified(result_weak)]
fn result_unimplied(){let x:u8=kani::any();assert_eq!(result_weak(x),Ok(x));}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.is_ok())]
fn result_badframe(x:&mut [u8;2])->Result<u8,u8>{x[1]=x[1].wrapping_add(1);Ok(0)}
#[kani::proof_for_contract(result_badframe)]
fn result_frame(){let mut x:[u8;2]=kani::any();result_badframe(&mut x);}
#[kani::requires(!x.is_empty())]
#[kani::ensures(|r| r.len()==1 && r[0]==x[0])]
fn slice_record(x:&[u8])->&[u8]{&x[..1]}
#[kani::requires(!x.is_empty())]
#[kani::ensures(|r| r.len()!=1)]
fn slice_invert(x:&[u8])->&[u8]{&x[..1]}
#[kani::proof_for_contract(slice_record)]
fn slice_positive(){let x:[u8;2]=kani::any();slice_record(&x);}
#[kani::proof_for_contract(slice_invert)]
fn slice_negative(){let x:[u8;2]=kani::any();slice_invert(&x);}
#[kani::requires(!x.is_empty())] #[kani::ensures(|r| r.len()==1)]
fn slice_weak(x:&[u8])->&[u8]{&x[..1]}
#[kani::proof_for_contract(slice_weak)]
fn slice_weak_proof(){let x:[u8;2]=kani::any();slice_weak(&x);}
#[kani::proof]
fn slice_real(){let x:[u8;2]=kani::any();assert_eq!(slice_weak(&x)[0],x[0]);}
#[kani::proof] #[kani::stub_verified(slice_weak)]
fn slice_unimplied(){let x:[u8;2]=kani::any();assert_eq!(slice_weak(&x)[0],x[0]);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.len()==1)]
fn slice_badframe(x:&mut [u8;2])->&[u8]{x[1]=x[1].wrapping_add(1);&x[..1]}
#[kani::proof_for_contract(slice_badframe)]
fn slice_frame(){let mut x:[u8;2]=kani::any();slice_badframe(&mut x);}
#[kani::requires(!x.is_empty())] #[kani::ensures(|r| r.as_ref().is_ok_and(|s| s.len()==1))]
fn result_slice_weak(x:&[u8])->Result<&[u8],u8>{Ok(&x[..1])}
#[kani::proof_for_contract(result_slice_weak)]
fn result_slice_positive(){let x:[u8;2]=kani::any();let _=result_slice_weak(&x);}
#[kani::proof] #[kani::stub_verified(result_slice_weak)]
fn result_slice_unimplied(){let x:[u8;2]=kani::any();assert_eq!(result_slice_weak(&x).unwrap()[0],x[0]);}
#[kani::ensures(|r| r.len()==1)]
fn vec_weak(x:u8)->Vec<u8>{let mut v=Vec::with_capacity(1);v.push(x);v}
#[kani::proof_for_contract(vec_weak)] #[kani::unwind(4)]
fn vec_positive(){let _=vec_weak(kani::any());}
#[kani::proof] #[kani::stub_verified(vec_weak)]
fn vec_unimplied(){let x:u8=kani::any();assert_eq!(vec_weak(x)[0],x);}
#[kani::ensures(|r| r.is_some())]
fn option_record_weak(x:u8)->Option<(u8,usize)>{Some((x,0))}
#[kani::proof_for_contract(option_record_weak)]
fn option_positive(){let _=option_record_weak(kani::any());}
#[kani::proof]
fn option_real(){let x:u8=kani::any();assert_eq!(option_record_weak(x),Some((x,0)));}
#[kani::proof] #[kani::stub_verified(option_record_weak)]
fn option_unimplied(){let x:u8=kani::any();assert_eq!(option_record_weak(x),Some((x,0)));}
#[kani::ensures(|r| r.is_none())]
fn option_record_invert(x:u8)->Option<(u8,usize)>{Some((x,0))}
#[kani::proof_for_contract(option_record_invert)]
fn option_negative(){let _=option_record_invert(kani::any());}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.is_some())]
fn option_badframe(x:&mut [u8;2])->Option<(u8,usize)>{x[1]=x[1].wrapping_add(1);Some((x[0],0))}
#[kani::proof_for_contract(option_badframe)]
fn option_frame(){let mut x:[u8;2]=kani::any();option_badframe(&mut x);}
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::requires(!x.is_empty())] #[kani::ensures(|r| r.is_err())]
fn result_slice_invert(x:&[u8])->Result<&[u8],u8>{Ok(&x[..1])}
#[kani::proof_for_contract(result_slice_invert)]
fn result_slice_negative(){let x:[u8;2]=kani::any();let _=result_slice_invert(&x);}
#[kani::proof]
fn result_slice_real(){let x:[u8;2]=kani::any();assert_eq!(result_slice_weak(&x).unwrap()[0],x[0]);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.is_ok())]
fn result_slice_badframe(x:&mut [u8;2])->Result<&[u8],u8>{x[1]=x[1].wrapping_add(1);Ok(&x[..1])}
#[kani::proof_for_contract(result_slice_badframe)]
fn result_slice_frame(){let mut x:[u8;2]=kani::any();let _=result_slice_badframe(&mut x);}
#[kani::ensures(|r| r.len()!=1)]
fn vec_invert(x:u8)->Vec<u8>{let mut v=Vec::with_capacity(1);v.push(x);v}
#[kani::proof_for_contract(vec_invert)] #[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn vec_negative(){let _=vec_invert(kani::any());}
#[kani::proof] #[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn vec_real(){let x:u8=kani::any();assert_eq!(vec_weak(x)[0],x);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.len()==1)]
fn vec_badframe(x:&mut [u8;2])->Vec<u8>{x[1]=x[1].wrapping_add(1);let mut v=Vec::with_capacity(1);v.push(x[0]);v}
#[kani::proof_for_contract(vec_badframe)] #[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn vec_frame(){let mut x:[u8;2]=kani::any();let _=vec_badframe(&mut x);}
