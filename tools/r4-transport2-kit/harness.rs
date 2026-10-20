#[cfg(kani)]
mod transport2 {
 use super::*;
 #[kani::proof]
 fn division_limb() {
  let word:u32=kani::any();let r:u64=kani::any();kani::assume(r<u64::from(P));
  let (q,rem)=division_step(word,r);
  let dividend=r*4294967296+u64::from(word);
  assert_eq!(u64::from(q),dividend/u64::from(P));
  assert_eq!(rem,dividend%u64::from(P));
  assert!(rem<u64::from(P));
 }
 #[kani::proof]
 fn addition_limb() {
  let word:u32=kani::any();let a:u32=kani::any();kani::assume(word<P);kani::assume(a<=257);
  let (digit,carry)=addition_step(word,a);
  let sum=u64::from(word)+u64::from(a);
  assert_eq!(u64::from(digit),sum%u64::from(P));
  assert_eq!(u64::from(carry),sum/u64::from(P));
  assert!(digit<P);assert!(carry<=1);
 }
 #[kani::proof]
 #[kani::unwind(10)]
 fn wide_iterator_order() {
  let rank:[u32;8]=kani::any();let mut q=rank;let mut j=8;
  for limb in q.iter_mut().rev() {
   j-=1;assert_eq!(*limb,rank[j]);*limb=j as u32;
  }
  assert_eq!(j,0);
  for i in 0..8 {assert_eq!(q[i],i as u32);}
  let mut next=0;
  let ds:[usize;8]=core::array::from_fn(|i| {assert_eq!(i,next);next+=1;i});
  assert_eq!(next,8);
  for i in 0..8 {assert_eq!(ds[i],i);}
 }
 #[kani::proof]
 #[kani::unwind(10)]
 fn addition_pass() {
  let input:[u32;8]=kani::any();let a:u32=kani::any();kani::assume(a<=257);
  for d in input {kani::assume(d<P);}
  let mut actual=input;let wrapped=add_small_base_p(&mut actual,a);
  let mut reference=input;let mut carry=u64::from(a);
  for i in 0..8 {
   let sum=u64::from(reference[i])+carry;
   reference[i]=(sum%u64::from(P)) as u32;
   carry=sum/u64::from(P);
  }
  assert_eq!(wrapped,carry==1);assert!(carry<=1);
  for i in 0..8 {assert_eq!(actual[i],reference[i]);assert!(actual[i]<P);}
 }
 // Every array write, stop branch and unchanged cell for one actual source word.
 fn scan_step<const N:usize>() {
  let accepted:[u32;22]=kani::any();let draws:usize=kani::any();let x:u32=kani::any();
  kani::assume(draws<=64);
  let mut actual=QueryScan{accepted,accepted_len:N,draws};
  let mut duplicate=false;
  for i in 0..N { if accepted[i]==x {duplicate=true;} }
  let stop=actual.step(x);
  assert_eq!(stop,N==22 || draws==64);
  let active=N<22 && draws<64;
  assert_eq!(actual.draws,draws+usize::from(active));
  assert_eq!(actual.accepted_len,N+usize::from(active && !duplicate));
  for i in 0..22 {
   assert_eq!(actual.accepted[i],if active && !duplicate && i==N {x} else {accepted[i]});
  }
 }
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_0() {scan_step::<0>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_1() {scan_step::<1>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_2() {scan_step::<2>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_3() {scan_step::<3>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_4() {scan_step::<4>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_5() {scan_step::<5>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_6() {scan_step::<6>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_7() {scan_step::<7>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_8() {scan_step::<8>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_9() {scan_step::<9>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_10() {scan_step::<10>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_11() {scan_step::<11>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_12() {scan_step::<12>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_13() {scan_step::<13>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_14() {scan_step::<14>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_15() {scan_step::<15>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_16() {scan_step::<16>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_17() {scan_step::<17>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_18() {scan_step::<18>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_19() {scan_step::<19>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_20() {scan_step::<20>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_21() {scan_step::<21>();}
 #[kani::proof]
 #[kani::unwind(24)]
 fn scan_step_22() {scan_step::<22>();}
}
