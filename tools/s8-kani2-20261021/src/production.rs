//! Production-capacity induction step, arbitrary cursor and probe cell.
use super::*;
fn q(a:[u32;4])->K {K{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}}}
fn coords(a:K)->[u32;4] {[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0]}
fn same(a:K,b:K) {assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);}
fn canonical(a:K)->bool {a.c0.a.0<0x7fffffff && a.c0.b.0<0x7fffffff && a.c1.a.0<0x7fffffff && a.c1.b.0<0x7fffffff}
#[kani::proof] #[kani::unwind(66)]
fn production_finish_step64() {
 let rows:[[u64;4];64]=kani::any();
 let old:[[u32;4];64]=kani::any();
 let cursor:usize=kani::any();let len:usize=kani::any();let probe:usize=kani::any();
 kani::assume(cursor<len && len<=64 && probe<64);
 let mut shipped=old.map(q);let mut reference=shipped;
 // Arbitrary probe represents the pointwise quantified prefix invariant.
 if probe<cursor {kani::assume(canonical(shipped[probe]));}
 let before=shipped[probe];
 let pending=BatchedWeights{raw:rows.to_vec(),terms:kani::any()};
 {
  let mut iterator=shipped[cursor..len].iter_mut().enumerate();
  let (relative,w)=iterator.next().unwrap();let i=cursor+relative;
  assert_eq!(i,cursor);
  *w=pending.value(i);
  assert_eq!(iterator.len(),len-cursor-1);
 }
 reference[cursor]=value_owned(rows[cursor]);
 same(shipped[probe],reference[probe]);
 if probe<cursor+1 {assert!(canonical(shipped[probe]));}
 if probe!=cursor {same(shipped[probe],before);}
 assert!(cursor+1<=len);
}
#[kani::proof] #[kani::unwind(66)]
fn production_finish_base64() {
 let old:[[u32;4];64]=kani::any();let len:usize=kani::any();let probe:usize=kani::any();
 kani::assume(len<=64 && probe<64);
 let mut shipped=old.map(q);let reference=shipped;
 assert_eq!(shipped[..len].iter_mut().enumerate().len(),len);
 same(shipped[probe],reference[probe]);
}
#[kani::proof] #[kani::unwind(66)]
fn production_finish_exit64() {
 let old:[[u32;4];64]=kani::any();let len:usize=kani::any();let probe:usize=kani::any();
 kani::assume(len<=64 && probe<64);
 let mut shipped=old.map(q);let before=shipped[probe];
 assert!(shipped[len..len].iter_mut().enumerate().next().is_none());
 same(shipped[probe],before);
}
