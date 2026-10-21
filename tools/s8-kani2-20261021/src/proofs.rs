//! One transition only; never invoke a whole finish traversal here.
use super::*;
fn q(a:[u32;4])->K {K{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}}}
fn coords(a:K)->[u32;4] {[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0]}
#[kani::proof] #[kani::unwind(20)]
fn finish_induction_step() {
 let rows:[[u64;4];3]=kani::any();
 let cursor:usize=kani::any();let len:usize=kani::any();
 kani::assume(cursor<len && len<=3);
 let old:[[u32;4];3]=kani::any();
 let mut shipped=[q(old[0]),q(old[1]),q(old[2])];
 let mut reference=shipped;
 // Symbolic invariant: every earlier cell is already a reduced output.
 // Cellwise equality/frame is universal over the three symbolic positions.
 for j in 0..3 { if j<cursor {kani::assume(old[j].iter().all(|x| *x<0x7fffffff));} }
 let pending=BatchedWeights{raw:rows.to_vec(),terms:kani::any()};
 {
  // The continuation state of the real IterMut: unconsumed suffix.
  let mut iterator=shipped[cursor..len].iter_mut().enumerate();
  let (relative,w)=iterator.next().unwrap();
  let i=cursor+relative;
  assert_eq!(i,cursor);
  // Literal shipped loop-body statement.
  *w=pending.value(i);
  assert_eq!(iterator.len(),len-cursor-1);
 }
 reference[cursor]=value_owned(rows[cursor]);
 let next=cursor+1;
 assert!(next<=len);
 for j in 0..3 {
  assert_eq!(coords(shipped[j]),coords(reference[j]));
  if j<next {assert!(coords(shipped[j]).iter().all(|x| *x<0x7fffffff));}
  if j!=cursor {assert_eq!(coords(shipped[j]),old[j]);}
 }
}
#[kani::proof] #[kani::unwind(20)]
fn finish_induction_base() {
 let old:[[u32;4];3]=kani::any();let len:usize=kani::any();kani::assume(len<=3);
 let mut shipped=[q(old[0]),q(old[1]),q(old[2])];let reference=shipped;
 let iterator=shipped[..len].iter_mut().enumerate();
 assert_eq!(iterator.len(),len);
 assert_eq!(reference.len(),3);
 // No prefix cells exist at cursor zero; suffix/frame is unchanged.
 for j in 0..3 {assert_eq!(coords(shipped[j]),coords(reference[j]));}
}
#[kani::proof] #[kani::unwind(20)]
fn finish_induction_exit() {
 let old:[[u32;4];3]=kani::any();let cursor:usize=kani::any();kani::assume(cursor<=3);
 let mut shipped=[q(old[0]),q(old[1]),q(old[2])];
 let before=shipped;
 assert!(shipped[cursor..cursor].iter_mut().enumerate().next().is_none());
 for j in 0..3 {assert_eq!(coords(shipped[j]),coords(before[j]));}
}
