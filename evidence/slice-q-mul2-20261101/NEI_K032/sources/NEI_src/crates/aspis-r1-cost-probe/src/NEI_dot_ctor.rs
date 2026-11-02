use super::*;
use super::super::EbyKDot;
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn dot_new() {
 let mut value=Dot::new();let lane:usize=kani::any();let observed:usize=kani::any();
 kani::assume(lane<4 && observed<4);
 let expected:u64=if cfg!(NEI_wrong_dot_ctor){1}else{0};
 assert_eq!(value.sums[observed],expected);
 let second=Dot::new();let replacement:u64=kani::any();value.sums[lane]=replacement;
 assert_eq!(second.sums[observed],0);
 assert_eq!(value.sums[observed],if lane==observed{replacement}else{0});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEI_copy::KMX_copy_nonoverlapping)]
fn eby_dot_new() {
 let mut value=EbyKDot::new();let side:bool=kani::any();let lane:usize=kani::any();let observed:usize=kani::any();
 kani::assume(lane<4 && observed<4);
 let got=if side{value.c0.sums[observed]}else{value.c1.sums[observed]};
 assert_eq!(got,if cfg!(NEI_wrong_eby_ctor){1}else{0});
 assert_eq!(value.count,0);
 let replacement:u64=kani::any();value.c0.sums[lane]=replacement;
 assert_eq!(value.c1.sums[observed],0);
 assert_eq!(value.c0.sums[observed],if lane==observed{replacement}else{0});
 assert_eq!(value.count,0);
}
