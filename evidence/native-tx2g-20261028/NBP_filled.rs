#[kani::proof]
#[kani::unwind(64)]
fn NBP_capacity_u8() {
 let n:usize=kani::any();kani::assume(n>(isize::MAX as usize)/1);
 let value:u8=kani::any();
 match super::filled(n,value) {Err(super::Error::Allocation)=>(),_=>assert!(false)}
 kani::cover!(n==usize::MAX);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_capacity_u32() {
 let n:usize=kani::any();kani::assume(n>(isize::MAX as usize)/4);
 let value:u32=kani::any();
 match super::filled(n,value) {Err(super::Error::Allocation)=>(),_=>assert!(false)}
 kani::cover!(n==usize::MAX);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_capacity_u64() {
 let n:usize=kani::any();kani::assume(n>(isize::MAX as usize)/8);
 let value:u64=kani::any();
 match super::filled(n,value) {Err(super::Error::Allocation)=>(),_=>assert!(false)}
 kani::cover!(n==usize::MAX);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_capacity_block() {
 let n:usize=kani::any();kani::assume(n>(isize::MAX as usize)/32);
 let value:[u8;32]=kani::any();
 match super::filled(n,value) {Err(super::Error::Allocation)=>(),_=>assert!(false)}
 kani::cover!(n==usize::MAX);
}
#[kani::proof]
#[kani::unwind(64)]
fn NBP_filled_zero() {
 let value:u64=kani::any();
 match super::filled(0,value) {Ok(v)=>{assert!(v.len()==0);assert!(v.capacity()==0);},_=>assert!(false)}
 kani::cover!(value==u64::MAX);
}
