//! Actual standard-container ownership transfers and allocation request shape.
use alloc::{boxed::Box,vec::Vec};
use core::{alloc::Layout,mem::{MaybeUninit,align_of,size_of,needs_drop}};
use aspis_core::field::{QM31,CM31,M31};
type Row=[QM31;29];type Claims=[Row;3];
fn row(raw:[[u32;4];29])->Row{
 let mut out=[QM31::ZERO;29];for j in 0..29{
  out[j]=QM31{c0:CM31{a:M31(raw[j][0]),b:M31(raw[j][1])},c1:CM31{a:M31(raw[j][2]),b:M31(raw[j][3])}};
 }out
}
#[kani::proof] #[kani::unwind(32)]
fn NP6_owned_transfers_and_layout(){
 assert!(size_of::<M31>()==4);assert!(size_of::<CM31>()==8);assert!(size_of::<QM31>()==16);
 assert!(size_of::<Row>()==464);assert!(size_of::<Claims>()==1392);assert!(align_of::<Claims>()==4);
 assert!(!needs_drop::<Claims>());assert!(!needs_drop::<MaybeUninit<Claims>>());
 let nl=Layout::array::<MaybeUninit<Claims>>(1).unwrap();
 let rl=Layout::array::<Row>(3).unwrap();
 assert!(nl.size()==rl.size());assert!(nl.align()==rl.align());
 let mut raw=Vec::<MaybeUninit<Claims>>::new();raw.try_reserve_exact(1).unwrap();assert!(raw.capacity()==1);
 let rows=[row(kani::any()),row(kani::any()),row(kani::any())];
 let mut native=aspis_core::r0::heap::uninit::<Claims>().unwrap();
 let original=native.as_mut_ptr();
 for p in 0..3 {unsafe{native.as_mut_ptr().cast::<Row>().add(p).write(rows[p]);}}
 let native=unsafe{native.assume_init()};assert!(core::ptr::eq(original,&*native));
 let values=aspis_core::r0::heap::filled(3,[QM31::ZERO;29]).unwrap();assert!(values.capacity()==3);
 let original=values.as_ptr();let slice=values.into_boxed_slice();assert!(core::ptr::eq(original,slice.as_ptr()));
 let owned:Box<Claims>=slice.try_into().unwrap();assert!(core::ptr::eq(original,owned.as_ptr()));
 let i=(kani::any::<u8>()as usize)%3;let j=(kani::any::<u8>()as usize)%29;
 assert!(native[i][j]==rows[i][j]);assert!(owned[i][j]==QM31::ZERO);
}
