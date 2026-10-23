// Pin-specific representation checks establish the public-constructor base
// case before the universally quantified private-state transition is used.
// No mirror is used by shipped code; these are verification-only observers.
use std::iter::StepBy;
use std::slice::Iter;
#[repr(C)] #[derive(Clone,Copy)]
struct IterRepr<T> { ptr:*const T,end:*const T }
#[repr(C)] #[derive(Clone,Copy)]
struct StepRepr<T> { iter:IterRepr<T>,step:usize,first:bool }
fn observe<T>(it:&StepBy<Iter<'_,T>>)->StepRepr<T> {
 assert_eq!(std::mem::size_of_val(it),std::mem::size_of::<StepRepr<T>>());
 unsafe { std::mem::transmute_copy(it) }
}
#[kani::requires(n<=256 && (k as usize)*2<(n as usize))]
#[kani::ensures(|r| r.0==data[(k as usize)*2] && r.1==(k as usize)*2+1 && !r.2)]
fn even_step(data:&[crate::field::QM31;256],n:u16,k:u8)->(crate::field::QM31,usize,bool) {
 let k=k as usize;let n=n as usize;
 let mut it:StepBy<Iter<'_,crate::field::QM31>>=if k==0 {data[..n].iter().step_by(2)} else {
  let state=StepRepr{iter:IterRepr{ptr:unsafe{data.as_ptr().add(2*k-1)},end:unsafe{data.as_ptr().add(n)}},step:1,first:false};
  unsafe {std::mem::transmute_copy(&state)}
 };
 let result=it.next().copied().unwrap();let state=observe(&it);
 assert_eq!(state.step,1);assert_eq!(state.iter.end,unsafe{data.as_ptr().add(n)});
 (result,unsafe{state.iter.ptr.offset_from(data.as_ptr())} as usize,state.first)
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(35)] fn constructor_layout() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();kani::assume(n<=256);
  let it=data[..n as usize].iter().step_by(2);let state=observe(&it);
  assert_eq!(state.iter.ptr,data.as_ptr());
  assert_eq!(state.iter.end,unsafe{data.as_ptr().add(n as usize)});
  assert_eq!(state.step,1);assert!(state.first);
 }
 #[kani::proof_for_contract(even_step)] #[kani::unwind(35)] fn even_transition() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();let k:u8=kani::any();
  kani::assume(n<=256 && (k as usize)*2<(n as usize));even_step(&data,n,k);
 }
 #[kani::proof] #[kani::stub_verified(even_step)] #[kani::unwind(35)] fn owned_iteration() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();let k:u8=kani::any();
  kani::assume(n<=256 && (k as usize)*2<(n as usize));
  let r=even_step(&data,n,k);
  assert_eq!(r.0,super::super::owned_read(&data[..n as usize],2,0,k as usize));
  assert_eq!(r.1,(k as usize+1)*2-1);assert!(!r.2);
 }
}
use std::iter::Skip;
#[repr(C)] #[derive(Clone,Copy)]
struct SkipRepr<T> { iter:IterRepr<T>,skip:usize }
#[repr(C)] #[derive(Clone,Copy)]
struct OddRepr<T> { iter:SkipRepr<T>,step:usize,first:bool }
fn observe_odd<T>(it:&StepBy<Skip<Iter<'_,T>>>)->OddRepr<T> {
 assert_eq!(std::mem::size_of_val(it),std::mem::size_of::<OddRepr<T>>());
 unsafe {std::mem::transmute_copy(it)}
}
#[kani::requires(n<=256 && (k as usize)*2+1<(n as usize))]
#[kani::ensures(|r| r.0==data[(k as usize)*2+1] && r.1==(k as usize)*2+2 && !r.2)]
fn odd_step(data:&[crate::field::QM31;256],n:u16,k:u8)->(crate::field::QM31,usize,bool) {
 let k=k as usize;let n=n as usize;
 let mut it:StepBy<Skip<Iter<'_,crate::field::QM31>>>=if k==0 {data[..n].iter().skip(1).step_by(2)} else {
  let state=OddRepr{iter:SkipRepr{iter:IterRepr{ptr:unsafe{data.as_ptr().add(2*k)},end:unsafe{data.as_ptr().add(n)}},skip:0},step:1,first:false};
  unsafe {std::mem::transmute_copy(&state)}
 };
 let result=it.next().copied().unwrap();let state=observe_odd(&it);
 assert_eq!(state.step,1);assert_eq!(state.iter.skip,0);assert_eq!(state.iter.iter.end,unsafe{data.as_ptr().add(n)});
 (result,unsafe{state.iter.iter.ptr.offset_from(data.as_ptr())} as usize,state.first)
}
#[cfg(kani)] mod odd_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(35)] fn constructor_layout() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();kani::assume(n<=256);
  let it=data[..n as usize].iter().skip(1).step_by(2);let state=observe_odd(&it);
  assert_eq!(state.iter.iter.ptr,data.as_ptr());assert_eq!(state.iter.iter.end,unsafe{data.as_ptr().add(n as usize)});
  assert_eq!(state.iter.skip,1);assert_eq!(state.step,1);assert!(state.first);
 }
 #[kani::proof_for_contract(odd_step)] #[kani::unwind(35)] fn odd_transition() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();let k:u8=kani::any();
  kani::assume(n<=256 && (k as usize)*2+1<(n as usize));odd_step(&data,n,k);
 }
 #[kani::proof] #[kani::stub_verified(odd_step)] #[kani::unwind(35)] fn owned_iteration() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();let k:u8=kani::any();
  kani::assume(n<=256 && (k as usize)*2+1<(n as usize));let r=odd_step(&data,n,k);
  assert_eq!(r.0,super::super::owned_read(&data[..n as usize],2,1,k as usize));
  assert_eq!(r.1,(k as usize+1)*2);assert!(!r.2);
 }
}
#[cfg(kani)] mod end_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(35)] fn exhausted() {
  let raw:[u32;1024]=kani::any();let data:[crate::field::QM31;256]=unsafe{std::mem::transmute(raw)};let n:u16=kani::any();kani::assume(n<=256 && n%2==0);let n=n as usize;
  let mut even:StepBy<Iter<'_,crate::field::QM31>>=if n==0 {data[..0].iter().step_by(2)} else {
   let state=StepRepr{iter:IterRepr{ptr:unsafe{data.as_ptr().add(n-1)},end:unsafe{data.as_ptr().add(n)}},step:1,first:false};
   unsafe{std::mem::transmute_copy(&state)}
  };
  assert!(even.next().is_none());let e=observe(&even);
  assert_eq!(e.iter.ptr,unsafe{data.as_ptr().add(n)});assert_eq!(e.iter.end,e.iter.ptr);assert!(!e.first);
  let mut odd:StepBy<Skip<Iter<'_,crate::field::QM31>>>=if n==0 {data[..0].iter().skip(1).step_by(2)} else {
   let state=OddRepr{iter:SkipRepr{iter:IterRepr{ptr:unsafe{data.as_ptr().add(n)},end:unsafe{data.as_ptr().add(n)}},skip:0},step:1,first:false};
   unsafe{std::mem::transmute_copy(&state)}
  };
  assert!(odd.next().is_none());let o=observe_odd(&odd);
  assert_eq!(o.iter.iter.ptr,unsafe{data.as_ptr().add(n)});assert_eq!(o.iter.iter.end,o.iter.iter.ptr);
  assert_eq!(o.iter.skip,0);assert!(!o.first);
 }
}
