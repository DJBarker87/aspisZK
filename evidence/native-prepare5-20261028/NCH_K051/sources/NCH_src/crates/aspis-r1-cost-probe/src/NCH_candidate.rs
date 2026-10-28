use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn NCH_vector(n:usize)->Vec<u8>{assert!(n<=256);let storage=Box::new(kani::any::<[u8;256]>());let ptr=Box::into_raw(storage).cast::<u8>();unsafe{Vec::from_raw_parts(ptr,n,256)}}
#[kani::requires(v.len()==n && n<256 && v.capacity()==256 && v.as_ptr()==base)]
#[kani::modifies(v,unsafe{v.as_mut_ptr().add(n)})]
#[kani::ensures(|_| v.len()==n+1 && v[n]==value && v.capacity()==256 && v.as_ptr()==base)]
fn NCH_push(v:&mut Vec<u8>,n:usize,value:u8,base:*const u8){v.push(value);}
#[kani::proof_for_contract(NCH_push)]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NCH_push_contract(){let n:usize=kani::any();kani::assume(n<256);let mut v=NCH_vector(n);let base=v.as_ptr();NCH_push(&mut v,n,kani::any(),base);}
#[kani::requires(v.len()==n && n<256 && v.capacity()==256 && v.as_ptr()==base)]
#[kani::modifies(v,unsafe{v.as_mut_ptr().add(n)})]
#[kani::ensures(|_| v.len()!=n+1)]
fn NCH_pushinvert(v:&mut Vec<u8>,n:usize,value:u8,base:*const u8){v.push(value);}
#[kani::proof_for_contract(NCH_pushinvert)]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NCH_push_inverted(){let n:usize=kani::any();kani::assume(n<256);let mut v=NCH_vector(n);let base=v.as_ptr();NCH_pushinvert(&mut v,n,kani::any(),base);}
#[kani::proof]#[kani::unwind(258)]#[kani::stub_verified(NCH_push)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_push_unimplied(){let n:usize=kani::any();kani::assume(0<n&&n<256);let mut v=NCH_vector(n);let base=v.as_ptr();let old=v[0];NCH_push(&mut v,n,kani::any(),base);assert_eq!(v[0],old,"prefix was not an ensures clause");}
#[kani::proof]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_push_real(){let n:usize=kani::any();kani::assume(0<n&&n<256);let mut v=NCH_vector(n);let base=v.as_ptr();let old=v[0];NCH_push(&mut v,n,kani::any(),base);assert_eq!(v[0],old);}
#[kani::requires(v.len()==n && n<256 && v.capacity()==256 && v.as_ptr()==base)]
#[kani::modifies(v)]
#[kani::ensures(|_| v.len()==n+1)]
fn NCH_pushbadframe(v:&mut Vec<u8>,n:usize,value:u8,base:*const u8){v.push(value);}
#[kani::proof_for_contract(NCH_pushbadframe)]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCH_push_modifies(){let n:usize=kani::any();kani::assume(n<256);let mut v=NCH_vector(n);let base=v.as_ptr();NCH_pushbadframe(&mut v,n,kani::any(),base);}
