#![allow(non_snake_case)]
#[cfg(test)] mod KSC2 {
use std::panic::{catch_unwind, AssertUnwindSafe};
#[test] fn option_result_branches() {
 assert_eq!(Some(3).ok_or(7), Ok(3)); assert_eq!(None::<i32>.ok_or(7), Err(7));
 let mut calls=0;
 assert_eq!(Ok::<_,i32>(3).unwrap_or_else(|_|{calls+=1;9}),3); assert_eq!(calls,0);
 assert_eq!(Err::<i32,_>(7).unwrap_or_else(|e|{calls+=1;e+2}),9); assert_eq!(calls,1);
 assert!(catch_unwind(|| Err::<i32,_>(7).unwrap_or_else(|_|panic!("expected unwrap closure panic"))).is_err());
 println!("ok_or: Some/None; unwrap_or_else: skip/call/panic");
}
#[test] fn iterator_defaults_and_range() {
 for n in [0,1,4] {
  let mut calls=Vec::new(); let mut r=0..n;
  let b=r.any(|x|{calls.push(x);x==1});
  assert_eq!(b,n>1); assert_eq!(calls,(0..n.min(2)).collect::<Vec<_>>()); assert_eq!(r.start,n.min(2));
  let mut r=0..n;assert_eq!(r.all(|x|x<1),n<=1);assert_eq!(r.start,n.min(2));
  let v=(0..n).map(|x|x+1).collect::<Vec<_>>();assert_eq!(v,(1..=n).collect::<Vec<_>>());
  assert_eq!((0..n).fold(0,|a,b|a*10+b),(0..n).collect::<Vec<_>>().into_iter().fold(0,|a,b|a*10+b));
  assert_eq!((0..n).enumerate().collect::<Vec<_>>(),(0..n).map(|x|(x as usize,x)).collect::<Vec<_>>());
  assert_eq!((0..n).rev().collect::<Vec<_>>(),(0..n).collect::<Vec<_>>().into_iter().rev().collect::<Vec<_>>());
  assert_eq!((0..n).step_by(2).collect::<Vec<_>>(),(0..n).filter(|x|x%2==0).collect::<Vec<_>>());
 }
 let mut n=0;let _lazy=(0..2).map(|x|{n+=1;x});assert_eq!(n,0);
 assert!(catch_unwind(||{let _=(0..3).step_by(0);}).is_err());
 assert!(catch_unwind(||{(0..3).any(|_|panic!("expected any closure panic"));}).is_err());
 assert!(catch_unwind(||{(0..3).fold(0,|_,_|panic!("expected fold closure panic"));}).is_err());
 println!("range/default: empty, exhaustive, early stop, stateful, lazy, zero step and closure panic");
}
#[test] fn shared_slice_and_windows_chunks() {
 for v in [vec![],vec![7],vec![1,2,3,4]] {
  let mut i=v.iter();let last=i.next_back().copied();assert_eq!(last,v.last().copied());
  assert_eq!(i.copied().collect::<Vec<_>>(),v[..v.len().saturating_sub(1)].to_vec());
  let mut i=v.iter();let _=i.next();let _=i.next_back();
  let want=if v.len()>1 {v[1..v.len()-1].to_vec()} else {vec![]};assert_eq!(i.copied().collect::<Vec<_>>(),want);
  assert_eq!(v.iter().fold(0,|a,b|a+b),v.iter().sum::<i32>());
  assert_eq!(v.iter().any(|x|*x==2),v.contains(&2));assert_eq!(v.iter().all(|x|*x<9),true);
  assert_eq!(v.iter().enumerate().map(|(i,x)|(i,*x)).collect::<Vec<_>>(),v.iter().copied().enumerate().collect::<Vec<_>>());
  assert_eq!(v.iter().rev().copied().collect::<Vec<_>>(),v.iter().copied().rev().collect::<Vec<_>>());
  assert_eq!(v.iter().step_by(2).copied().collect::<Vec<_>>(),v.iter().copied().enumerate().filter_map(|(i,x)|(i%2==0).then_some(x)).collect::<Vec<_>>());
  for w in [1,2,5] {
   let ws=v.windows(w).map(|s|s.to_vec()).collect::<Vec<_>>();
   assert_eq!(ws.len(),v.len().checked_sub(w).map(|n|n+1).unwrap_or(0));
   let mut iter=v.windows(w);let _=iter.all(|s|s[0]!=2);let rest=iter.count();assert!(rest<=ws.len());
   let mut chunks=v.chunks_exact(w);let b=chunks.any(|c|c[0]==2);assert_eq!(b,v.chunks_exact(w).any(|c|c[0]==2));assert_eq!(chunks.remainder(),&v[v.len()/w*w..]);
  }
 }
 assert!(catch_unwind(||{let _=[1].windows(0);}).is_err());
 assert!(catch_unwind(||{let _=[1].chunks_exact(0);}).is_err());
 println!("shared next_back incl crossed cursors; windows empty/one/overlap/oversize/zero; chunks remainder/zero");
}
#[test] fn mutable_borrow_writeback_counterexamples() {
 let mut a=[7];let mut it=a.iter_mut();assert_eq!(it.next().map(|x|*x),Some(7));assert_eq!(it.next_back().map(|x|*x),None);
 println!("next_back after next on [7]: native None, kit Some(7)");
 let mut a=[1,2];let mut it=a.iter_mut();assert!(it.any(|x|{*x+=10;true}));assert_eq!(it.next().map(|x|*x),Some(2));drop(it);assert_eq!(a,[11,2]);
 let mut b=[1,2];let mut it=b.iter_mut();assert!(!it.all(|x|{*x+=10;false}));drop(it);assert_eq!(b,[11,2]);
 let mut c=[1,2];let s=c.iter_mut().fold(0,|n,x|{*x+=10;n+*x});assert_eq!(s,23);assert_eq!(c,[11,12]);
 println!("any/all short-circuit retain [11,2]; fold retains [11,12]; kit callbacks have no item write-back channel");
 let mut a=[1,2];let refs=a.iter_mut().collect::<Vec<_>>();for x in refs {*x+=10;}assert_eq!(a,[11,12]);
 let mut a=[1,2,3];for (i,x) in a.iter_mut().enumerate(){*x+=i as i32;}assert_eq!(a,[1,3,5]);
 let mut a=[1,2,3];for x in a.iter_mut().step_by(2){*x+=10;}assert_eq!(a,[11,2,13]);
 let mut a=[1,2];let mut it=a.iter_mut().rev();*it.next().unwrap()=20;*it.next().unwrap()=10;assert!(it.next().is_none());drop(it);assert_eq!(a,[10,20]);
 let mut a=[1,2,3];for c in a.chunks_exact_mut(2){c[0]=10;c[1]=20;}assert_eq!(a,[10,20,3]);
 assert!(catch_unwind(AssertUnwindSafe(||{let _=[1,2].iter_mut().step_by(0);})).is_err());
 println!("collect/enumerate/step_by/rev/chunks_exact_mut preserve mutable aliases; zero step panics");
}
#[test] fn from_fn_and_array_slice_controls() {
 let mut state=0;let a:[i32;3]=std::array::from_fn(|i|{state+=1;10*state+i as i32});assert_eq!(a,[10,21,32]);assert_eq!(state,3);
 let z:[i32;0]=std::array::from_fn(|_|panic!("zero-length must not call"));assert_eq!(z,[]);
 let mut calls=0;assert!(catch_unwind(AssertUnwindSafe(||{let _:[i32;3]=std::array::from_fn(|i|{calls+=1;if i==1 {panic!("expected from_fn panic")};i as i32});})).is_err());assert_eq!(calls,2);
 let s=[1,2,3];assert_eq!(<[i32;3]>::try_from(s.as_slice()).unwrap(),s);assert!(<[i32;2]>::try_from(s.as_slice()).is_err());assert_eq!(<[i32;0]>::try_from(&[][..]).unwrap(),[]);
 let mut s=[1,2];let r:&mut [i32;2]=s.as_mut_slice().try_into().unwrap();r[1]=9;assert_eq!(s,[1,9]);
 println!("from_fn ascending state/empty/panic; slice-array length match/mismatch/empty/mut restore (cross-split controls)");
}
#[test] fn additional_branches() {
 let mut a:[i32;0]=[];
 assert!(!a.iter_mut().any(|_|panic!("empty any")));
 assert!(a.iter_mut().all(|_|panic!("empty all")));
 assert_eq!(a.iter_mut().fold(17,|_,_|panic!("empty fold")),17);
 let mut a=[1,2]; assert!(!a.iter_mut().any(|x|{*x+=10;false})); assert_eq!(a,[11,12]);
 let mut a=[1,2]; assert!(a.iter_mut().all(|x|{*x+=10;true})); assert_eq!(a,[11,12]);
 let mut i=[1,2,3].iter();assert!(!i.all(|x|*x!=2));assert_eq!(i.copied().collect::<Vec<_>>(),[3]);
 let mut i=[1,2,3].iter();assert!(!i.any(|x|*x>10));assert!(i.next().is_none());
 assert!(catch_unwind(||{[1,2].iter().all(|_|panic!("expected all panic"));}).is_err());
 assert!(catch_unwind(||{[1,2].windows(1).all(|_|panic!("expected windows panic"));}).is_err());
 assert!(catch_unwind(||{[1,2].chunks_exact(1).any(|_|panic!("expected chunks panic"));}).is_err());
 for which in 0..3 {
  let mut a=[1,2];
  assert!(catch_unwind(AssertUnwindSafe(|| {
   match which {
    0=>{a.iter_mut().any(|x|{*x=9;panic!("expected mut any panic")});},
    1=>{a.iter_mut().all(|x|{*x=9;panic!("expected mut all panic")});},
    _=>{a.iter_mut().fold(0,|_,x|{*x=9;panic!("expected mut fold panic")});}
   }
  })).is_err());assert_eq!(a,[9,2]);
 }
 let mut consumed=Vec::new();
 let result=(0..4).map(|x|{consumed.push(x);if x==2 {Err(x)} else {Ok(x)}}).collect::<Result<Vec<_>,_>>();
 assert_eq!(result,Err(2));assert_eq!(consumed,[0,1,2]);
 assert!(catch_unwind(||{let _=(0..3).map(|_|panic!("expected map collect panic")).collect::<Vec<i32>>();}).is_err());
 println!("additional branches: empty/exhaustive mutable any/all/fold; shared early stop; callback panic retains prefix writes; Result collect stops on Err");
}

#[test] fn finite_small_domain() {
 let mut cases=0;
 for n in 0..=4u32 {
  for code in 0..3u32.pow(n) {
   let mut q=code;
   let original=(0..n).map(|_|{let x=(q%3) as i32;q/=3;x}).collect::<Vec<_>>();
   for stop in 0..=3i32 {
    let mut a=original.clone();let b=a.iter_mut().any(|x|{let old=*x;*x+=10;old==stop});
    let mut expected=original.clone();let mut eb=false;
    for x in &mut expected {let old=*x;*x+=10;if old==stop {eb=true;break;}}
    assert_eq!((b,a),(eb,expected));
    let mut a=original.clone();let b=a.iter_mut().all(|x|{let old=*x;*x+=10;old!=stop});
    let mut expected=original.clone();let mut eb=true;
    for x in &mut expected {let old=*x;*x+=10;if old==stop {eb=false;break;}}
    assert_eq!((b,a),(eb,expected));
   }
   let mut a=original.clone();let total=a.iter_mut().fold(0,|sum,x|{*x+=10;sum+*x});
   let expected=original.iter().map(|x|x+10).collect::<Vec<_>>();
   assert_eq!(total,expected.iter().sum::<i32>());assert_eq!(a,expected);
   for front in 0..=n {
    let mut a=original.clone();let mut it=a.iter_mut();
    for _ in 0..front {let _=it.next();}
    for expected in original[front as usize..].iter().rev() {
     assert_eq!(it.next_back().map(|x|*x),Some(*expected));
    }
    assert_eq!(it.next_back().map(|x|*x),None);
   }
   cases+=1;
  }
 }
 assert_eq!(cases,121);
 println!("121 finite list fixtures, all 4 stop values, mutable any/all/fold poststate, every front-cursor/back-exhaustion combination; fixture coverage only");
}

}
