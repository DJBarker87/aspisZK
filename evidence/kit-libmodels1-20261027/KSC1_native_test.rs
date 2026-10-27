// Standalone scratch cfg(test) module; real Rust 1.94.1 std calls.
#[cfg(test)] mod KSC1 {
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::cell::Cell;
#[test] fn mixed_direction_and_restore() {
 let mut a=[7u8]; let mut it=a.iter_mut(); assert_eq!(it.next().map(|x|*x),Some(7));
 assert_eq!(it.next_back().map(|x|*x),None); assert_eq!(it.next().map(|x|*x),None);
 println!("singleton: native next=Some(7), next_back=None; kit next_back=Some(7)");
 for n in 0..=4 {
  let mut a:Vec<i32>=(0..n).collect(); let original=a.clone();
  {let mut it=a.iter_mut(); if let Some(x)=it.next(){*x+=10;} if let Some(x)=it.next_back(){*x+=20;} for x in it.rev(){*x+=30;}}
  let mut expected=original; if n>0 {expected[0]+=10;} if n>1 {expected[(n-1)as usize]+=20;} if n>2 {for x in &mut expected[1..(n-1) as usize]{*x+=30;}}
  assert_eq!(a,expected);
 }
 let mut a=[1,2,3]; for (i,x) in a.iter_mut().enumerate(){*x+=i as i32;} assert_eq!(a,[1,3,5]);
 let mut a=[1,2,3]; for x in a.iter_mut().rev(){*x*=2;} assert_eq!(a,[2,4,6]);
 let mut a=[1,2,3,4,5]; for c in a.chunks_exact_mut(2){c[0]+=10;c[1]+=20;} assert_eq!(a,[11,22,13,24,5]);
 let mut a=[1,2]; let r:Vec<_>=(&mut a).into_iter().map(|x|{*x+=10;*x}).collect();assert_eq!(r,[11,12]);assert_eq!(a,[11,12]);
 println!("writeback: front/back/rev/enumerate/chunks_exact_mut/array_into_iter passed");
}
#[test] fn from_fn_and_map_state_and_panic() {
 let calls=Cell::new(0);let empty:[usize;0]=std::array::from_fn(|_|{calls.set(calls.get()+1);0});assert_eq!(empty,[]);assert_eq!(calls.get(),0);
 let mut state=1;let mut trace=Vec::new();let a:[usize;4]=std::array::from_fn(|i|{trace.push(i);let old=state;state*=2;old});assert_eq!(a,[1,2,4,8]);assert_eq!(state,16);assert_eq!(trace,[0,1,2,3]);
 let mut trace=Vec::new();let a=[1,2,3].map(|x|{trace.push(x);x*10});assert_eq!(a,[10,20,30]);assert_eq!(trace,[1,2,3]);
 let drops=Cell::new(0);struct D<'a>(&'a Cell<i32>);impl Drop for D<'_>{fn drop(&mut self){self.0.set(self.0.get()+1);}}
 let mut trace=Vec::new();let r=catch_unwind(AssertUnwindSafe(||{let _: [D<'_>;4]=std::array::from_fn(|i|{trace.push(i);if i==2{panic!("branch panic");}D(&drops)});}));assert!(r.is_err());assert_eq!(trace,[0,1,2]);assert_eq!(drops.get(),2);
 println!("from_fn: empty/no callback, ascending state=[1,2,4,8]/final16, panic prefix=[0,1,2]/drops2; map state passed");
}
#[test] fn equality_empty_collect_fold_all() {
 assert!(Vec::<u8>::new().is_empty());assert!(!vec![1u8].is_empty());
 for (a,b,same) in [(vec![],[1,2],false),(vec![1],[1,2],false),(vec![1,2],[1,2],true),(vec![1,3],[1,2],false)]{assert_eq!(a.as_slice()==b,same);assert_eq!(a.as_slice()!=b,!same);}
 let p=[1,2,3];let mut seen=Vec::new();let r:Vec<_>=p.iter().map(|x|{seen.push(*x);x*2}).collect();assert_eq!(r,[2,4,6]);assert_eq!(seen,p);
 let empty:Vec<i32>=[].into_iter().map(|x:i32|x+1).collect();assert!(empty.is_empty());
 let mut seen=Vec::new();let r=p.iter().rev().fold(0,|acc,x|{seen.push(*x);acc*10+x});assert_eq!(r,321);assert_eq!(seen,[3,2,1]);
 assert_eq!([].into_iter().rev().fold(5,|a,x:i32|a+x),5);
 for (p,want,remaining,expect_calls) in [(vec![],true,None,vec![]),(vec![1,2],true,None,vec![1,2]),(vec![1,3,2],false,Some(2),vec![1,3])] {
  let mut calls=Vec::new();let mut it=p.into_iter();assert_eq!(it.all(|x|{calls.push(x);x<3}),want);assert_eq!(it.next(),remaining);assert_eq!(calls,expect_calls);
 }
 let mut calls=Vec::new();let r=catch_unwind(AssertUnwindSafe(||{[1,2,3].into_iter().all(|x|{calls.push(x);if x==2{panic!("predicate panic");}true})}));assert!(r.is_err());assert_eq!(calls,[1,2]);
 let mut calls=Vec::new();let r=catch_unwind(AssertUnwindSafe(||{let _:Vec<_>=[1,2,3].into_iter().map(|x|{calls.push(x);if x==2{panic!("map panic");}x}).collect();}));assert!(r.is_err());assert_eq!(calls,[1,2]);
 println!("eq/ne length/equal/mismatch; empty; collect/fold/all empty/continuation/short-circuit/panic passed");
}
#[test] fn additional_failure_branches() {
 let drops=Cell::new(0);struct D<'a>(&'a Cell<i32>);impl Drop for D<'_>{fn drop(&mut self){self.0.set(self.0.get()+1);}}
 let mut seen=Vec::new();let r=catch_unwind(AssertUnwindSafe(||{let a=[D(&drops),D(&drops),D(&drops)];let _=a.map(|x|{seen.push(seen.len());if seen.len()==2{panic!("array map panic");}x});}));assert!(r.is_err());assert_eq!(seen,[0,1]);assert_eq!(drops.get(),3);
 let mut seen=Vec::new();let r=catch_unwind(AssertUnwindSafe(||{[1,2,3].into_iter().rev().fold(0,|a,x|{seen.push(x);if x==2{panic!("fold panic");}a+x})}));assert!(r.is_err());assert_eq!(seen,[3,2]);
 for stop in [0,3] {let mut seen=Vec::new();let r=catch_unwind(AssertUnwindSafe(||{let _: [usize;4]=std::array::from_fn(|i|{seen.push(i);if i==stop{panic!("edge panic");}i});}));assert!(r.is_err());assert_eq!(seen,(0..=stop).collect::<Vec<_>>());}
 let empty:[u8;0]=[];assert!(empty.as_slice()==empty);assert!(!(empty.as_slice()!=empty));
 let mut empty:[u8;0]=[];assert_eq!(empty.iter_mut().next_back(),None);assert_eq!(empty.iter_mut().enumerate().next(),None);
 println!("array map panic/drop3, reversed-fold panic prefix, from_fn first/last panic, empty equality/borrowed-iteration passed");
}

}
