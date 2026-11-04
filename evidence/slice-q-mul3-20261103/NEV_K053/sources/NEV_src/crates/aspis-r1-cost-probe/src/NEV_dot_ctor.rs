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
// Owned receiver logs replace two already isolated Dot::push calls.
struct NEV_DotLog { receiver:usize,old:[u64;4],a:[u32;4],b:[u32;4],reply:[u64;4],calls:u8,order:u8 }
impl NEV_DotLog {
 fn call(&mut self,receiver:&mut Dot,a:Q,b:Q,phase:&mut u8) {
  self.receiver=receiver as *mut Dot as usize;self.old=receiver.sums;self.a=a.0;self.b=b.0;
  self.calls+=1;self.order=*phase;*phase+=1;receiver.sums=self.reply;
 }
}
fn NEV_eby_cut(value:&mut EbyKDot,wide:super::super::E,scalar:super::super::QM31,l:&mut NEV_DotLog,r:&mut NEV_DotLog,phase:&mut u8)->Result<(),()> {
 if value.count>=4096{return Err(());}
 let [value_c0,value_c1]=Q::from_wide(wide);
 let scalar=super::super::checked_q(scalar)?;
 l.call(&mut value.c0,value_c0,scalar,phase);r.call(&mut value.c1,value_c1,scalar,phase);
 value.count+=1;Ok(())
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn eby_push_context() {
 let wide:[u32;8]=kani::any();for x in wide{kani::assume(x<P);}
 let scalar:[u32;4]=kani::any();let left:[u64;4]=kani::any();let right:[u64;4]=kani::any();let count:usize=kani::any();
 let mut value=EbyKDot{c0:Dot{sums:left},c1:Dot{sums:right},count};
 let leftptr=&mut value.c0 as *mut Dot as usize;let rightptr=&mut value.c1 as *mut Dot as usize;
 let mut l=NEV_DotLog{receiver:0,old:[0;4],a:[0;4],b:[0;4],reply:kani::any(),calls:0,order:99};
 let mut r=NEV_DotLog{receiver:0,old:[0;4],a:[0;4],b:[0;4],reply:kani::any(),calls:0,order:99};
 let mut phase=0;let got=NEV_eby_cut(&mut value,super::super::E::from_limbs(wide).unwrap(),super::super::QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(scalar[0]),b:aspis_core::field::M31(scalar[1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(scalar[2]),b:aspis_core::field::M31(scalar[3])}},&mut l,&mut r,&mut phase);
 let valid=scalar[0]<P && scalar[1]<P && scalar[2]<P && scalar[3]<P;let active=count<4096 && valid;
 assert_eq!(got.is_ok(),active);let observed:usize=kani::any();kani::assume(observed<4);
 if active {
  assert_eq!(l.calls,1);assert_eq!(r.calls,1);assert_eq!(phase,2);assert_eq!(l.order,0);assert_eq!(r.order,1);
  assert_eq!(l.receiver,leftptr);assert_eq!(r.receiver,rightptr);assert_eq!(l.old,left);assert_eq!(r.old,right);
  assert_eq!(l.a,[wide[0],wide[1],wide[2],wide[3]]);assert_eq!(r.a,[wide[4],wide[5],wide[6],wide[7]]);
  assert_eq!(l.b,scalar);assert_eq!(r.b,scalar);assert_eq!(value.c0.sums[observed],l.reply[observed]);assert_eq!(value.c1.sums[observed],r.reply[observed]);
 }else{
  assert_eq!(l.calls,0);assert_eq!(r.calls,0);assert_eq!(phase,0);assert_eq!(value.c0.sums[observed],left[observed]);assert_eq!(value.c1.sums[observed],right[observed]);
 }
 let expected=if active{count+1}else{count};assert_eq!(value.count,if cfg!(NEV_wrong_eby_context){expected^1}else{expected});
}
