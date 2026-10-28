use zeroize::Zeroizing;
use std::{mem::MaybeUninit,hint::black_box,sync::atomic::{compiler_fence,Ordering}};
#[repr(C)]struct Guard<const N:usize>{before:[u8;11],value:MaybeUninit<Zeroizing<[u8;N]>>,after:[u8;13]}
fn test<const N:usize>()->usize{for seed in 0..=255u8{
 let input=std::array::from_fn(|i|seed.wrapping_add((i as u8).wrapping_mul(37)));
 let mut slot=Guard{before:[0xa5;11],value:MaybeUninit::new(Zeroizing::new(input)),after:[0x5a;13]};
 // The MaybeUninit allocation remains live after drop_in_place. The pointer
 // addresses initialized u8 bytes, not a read of a destroyed owning value;
 // MaybeUninit prevents a second destructor call at scope exit.
 let p=unsafe{slot.value.assume_init_mut().as_mut_ptr()};
 unsafe{std::ptr::drop_in_place(black_box(slot.value.as_mut_ptr()));}
 let mut reference=input;for x in &mut reference{unsafe{std::ptr::write_volatile(x,0)};compiler_fence(Ordering::SeqCst);}
 let observed:[u8;N]=std::array::from_fn(|i|unsafe{black_box(p.add(i)).read_volatile()});
 assert_eq!(observed,reference);assert_eq!(observed,[0;N]);assert_eq!(slot.before,[0xa5;11]);assert_eq!(slot.after,[0x5a;13]);
 }256}
fn main(){let n=test::<0>()+test::<1>()+test::<32>()+test::<64>();println!("PASS {n} paired actual Zeroizing<[u8;N]>::drop cases in live MaybeUninit storage, target zero and neighbors intact; finite validation of consumed destructor path, not full binary erasure");}
