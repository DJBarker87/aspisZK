use super::*;
use super::super::EbyKDot;
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dot_new() {
 let mut value=Dot::new();let lane:usize=kani::any();let observed:usize=kani::any();
 kani::assume(lane<4 && observed<4);
 let expected:u64=if cfg!(NEV_wrong_dot_ctor){1}else{0};
 assert_eq!(value.sums[observed],expected);
 let second=Dot::new();let replacement:u64=kani::any();value.sums[lane]=replacement;
 assert_eq!(second.sums[observed],0);
 assert_eq!(value.sums[observed],if lane==observed{replacement}else{0});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn eby_dot_new() {
 let mut value=EbyKDot::new();let side:bool=kani::any();let lane:usize=kani::any();let observed:usize=kani::any();
 kani::assume(lane<4 && observed<4);
 let got=if side{value.c0.sums[observed]}else{value.c1.sums[observed]};
 assert_eq!(got,if cfg!(NEV_wrong_eby_ctor){1}else{0});
 assert_eq!(value.count,0);
 let replacement:u64=kani::any();value.c0.sums[lane]=replacement;
 assert_eq!(value.c1.sums[observed],0);
 assert_eq!(value.c0.sums[observed],if lane==observed{replacement}else{0});
 assert_eq!(value.count,0);
}

// Safe scalar reference transliterating the coherent reducer, using wrapping
// additions/subtraction. The actual frozen reducer uses checked source ops.
fn NEV_reduce_ref(mut x:u64)->u32 {
 x=(x & u64::from(P)).wrapping_add(x>>31u32);
 x=(x & u64::from(P)).wrapping_add(x>>31u32);
 if x>=u64::from(P) {x.wrapping_sub(u64::from(P)) as u32}else{x as u32}
}
#[kani::proof]
fn reduce_word() {
 let input:u64=kani::any();let got=reduce(input);let expected=NEV_reduce_ref(input);
 assert_eq!(got,if cfg!(NEV_wrong_reduce_word){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dot_finish() {
 let words:[u64;4]=kani::any();let got=Dot{sums:words}.finish().limbs();
 let mut expected=[0u32;4];for at in 0..4 {expected[at]=NEV_reduce_ref(words[at]);}
 if cfg!(NEV_wrong_dot_finish){expected[0]^=1;}
 assert_eq!(got,expected);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn eby_dot_finish() {
 let left:[u64;4]=kani::any();let right:[u64;4]=kani::any();let count:usize=kani::any();
 let actual=EbyKDot{c0:Dot{sums:left},c1:Dot{sums:right},count}.finish();
 let got=actual.to_limbs();let mut expected=[0u32;8];
 for at in 0..4 {expected[at]=NEV_reduce_ref(left[at]);expected[at+4]=NEV_reduce_ref(right[at]);}
 if cfg!(NEV_wrong_eby_finish){expected[0]^=1;}
 assert_eq!(got,expected);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn q_limbs() {
 let words:[u32;4]=kani::any();let got=Q(words).limbs();let mut expected=words;
 if cfg!(NEV_wrong_q_limbs){expected[0]^=1;}
 assert_eq!(got,expected);
}
// Receipt-only replay source; compiled solely from cfg(kani) scratch module.
struct NEV_RawLog { a:[u32;4],b:[u32;4],reply:[u64;4],calls:u8 }
impl NEV_RawLog {
 fn call(&mut self,a:Q,b:Q)->[u64;4] {self.a=a.0;self.b=b.0;self.calls+=1;self.reply}
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn dot_push_iteration() {
 let before:[u64;4]=kani::any();let left:[u32;4]=kani::any();let right:[u32;4]=kani::any();
 for k in 0..4 {kani::assume(left[k]<P && right[k]<P);}
 let index:usize=kani::any();let observed:usize=kani::any();kani::assume(index<4 && observed<4);
 let reply:[u64;4]=kani::any();let mut log=NEV_RawLog{a:[0;4],b:[0;4],reply,calls:0};
 let mut dot=Dot{sums:before};let raw=log.call(Q(left),Q(right));
 let mut cursor=index..4;let j=cursor.next().unwrap();
 // Literal native ONE-iteration body; raw arithmetic is an opaque owned call.
 dot.sums[j]=dot.sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31u32));
 assert_eq!(cursor.start,index+1);assert_eq!(cursor.end,4);
 assert_eq!(log.calls,1);assert_eq!(log.a,left);assert_eq!(log.b,right);
 let expected=if observed==index {before[observed].wrapping_add((reply[observed]&u64::from(P)).wrapping_add(reply[observed]>>31u32))}else{before[observed]};
 assert_eq!(dot.sums[observed],if cfg!(NEV_wrong_dot_iteration){expected^1}else{expected});
}
