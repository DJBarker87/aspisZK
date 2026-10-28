use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Restricted FIRST append only; no arbitrary live-prefix result is claimed.
#[kani::requires(v.len()==0 && v.capacity()==256 && v.as_ptr()==base)]
#[kani::modifies(v,v.as_mut_ptr())]
#[kani::ensures(|_| v.len()==1 && v[0]==value && v.capacity()==256 && v.as_ptr()==base)]
fn NCH_pushfirst(v:&mut Vec<u8>,value:u8,base:*const u8){v.push(value);}
#[kani::proof_for_contract(NCH_pushfirst)]#[kani::unwind(3)]
fn NCH_first_contract(){let mut v=Vec::<u8>::with_capacity(256);let base=v.as_ptr();NCH_pushfirst(&mut v,kani::any(),base);}
#[kani::requires(v.len()==0 && v.capacity()==256 && v.as_ptr()==base)]
#[kani::modifies(v,v.as_mut_ptr())]#[kani::ensures(|_| v.len()!=1)]
fn NCH_firstinvert(v:&mut Vec<u8>,value:u8,base:*const u8){v.push(value);}
#[kani::proof_for_contract(NCH_firstinvert)]#[kani::unwind(3)]
fn NCH_first_inverted(){let mut v=Vec::<u8>::with_capacity(256);let base=v.as_ptr();NCH_firstinvert(&mut v,kani::any(),base);}
#[kani::requires(v.len()==0 && v.capacity()==256)]
#[kani::modifies(v,v.as_mut_ptr())]#[kani::ensures(|_| v.len()==1)]
fn NCH_firstweak(v:&mut Vec<u8>,value:u8){v.push(value);}
#[kani::proof_for_contract(NCH_firstweak)]#[kani::unwind(3)]
fn NCH_first_weak_contract(){let mut v=Vec::<u8>::with_capacity(256);NCH_firstweak(&mut v,kani::any());}
#[kani::proof]#[kani::unwind(3)]#[kani::stub_verified(NCH_firstweak)]
fn NCH_first_unimplied(){let mut v=Vec::<u8>::with_capacity(256);NCH_firstweak(&mut v,kani::any());let cap=v.capacity();core::mem::forget(v);assert_eq!(cap,256,"weak contract has no capacity postcondition");}
#[kani::proof]#[kani::unwind(3)]
fn NCH_first_real(){let mut v=Vec::<u8>::with_capacity(256);NCH_firstweak(&mut v,kani::any());let cap=v.capacity();core::mem::forget(v);assert_eq!(cap,256);}
#[kani::requires(v.len()==0 && v.capacity()==256 && v.as_ptr()==base)]
#[kani::modifies(v)]#[kani::ensures(|_| v.len()==1)]
fn NCH_firstbadframe(v:&mut Vec<u8>,value:u8,base:*const u8){v.push(value);}
#[kani::proof_for_contract(NCH_firstbadframe)]#[kani::unwind(3)]
fn NCH_first_modifies(){let mut v=Vec::<u8>::with_capacity(256);let base=v.as_ptr();NCH_firstbadframe(&mut v,kani::any(),base);}
#[kani::proof]#[kani::unwind(3)]#[kani::stub_verified(NCH_pushfirst)]
fn NCH_first_caller(){let source:[u8;32]=kani::any();let mut v=Vec::<u8>::with_capacity(256);let base=v.as_ptr();v.reserve(32);NCH_pushfirst(&mut v,source[0],base);assert_eq!(v[0],source[0]);assert_eq!(v.len(),1);assert_eq!(v.capacity(),256);assert_eq!(v.as_ptr(),base);}
#[kani::proof]#[kani::unwind(3)]#[kani::stub_verified(NCH_pushfirst)]
fn NCH_first_caller_wrong(){let mut v=Vec::<u8>::with_capacity(256);let base=v.as_ptr();v.reserve(32);NCH_pushfirst(&mut v,1,base);assert_eq!(v[0],0);}
