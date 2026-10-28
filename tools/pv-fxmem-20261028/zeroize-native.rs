use zeroize::Zeroize;
use std::{hint::black_box,sync::atomic::{compiler_fence,Ordering}};
fn reference(xs:&mut [u8]){for x in xs {unsafe{std::ptr::write_volatile(x,0)};compiler_fence(Ordering::SeqCst);}}
#[repr(C)] struct Guard<const N:usize>{before:[u8;11],target:[u8;N],after:[u8;13]}
fn test<const N:usize>()->usize{for seed in 0..=255u8 {
 let input=std::array::from_fn(|i|seed.wrapping_add((i as u8).wrapping_mul(37)));
 let mut native=Guard{before:[0xa5;11],target:input,after:[0x5a;13]};
 let mut owned=Guard{before:[0xa5;11],target:input,after:[0x5a;13]};
 black_box(&mut native.target).zeroize();reference(black_box(&mut owned.target));
 assert_eq!(native.target,[0;N]);assert_eq!(native.target,owned.target);
 assert_eq!(native.before,owned.before);assert_eq!(native.after,owned.after);
 assert_eq!(native.before,[0xa5;11]);assert_eq!(native.after,[0x5a;13]);
 let mut byte=black_box(seed);byte.zeroize();assert_eq!(byte,0);
 }256}
fn main(){let count=test::<0>()+test::<1>()+test::<2>()+test::<32>()+test::<64>();println!("PASS {count} array pairs and {count} byte cases, all target bytes zero and adjacent frames intact; finite validation, not machine non-elision audit");}
