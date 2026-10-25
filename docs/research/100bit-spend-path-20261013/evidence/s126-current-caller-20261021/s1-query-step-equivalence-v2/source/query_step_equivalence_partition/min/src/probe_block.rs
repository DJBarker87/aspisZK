#![no_std]
extern crate alloc;
fn owned_contains(a:&[u32;22],len:usize,candidate:u32)->bool{
 let mut j=0;while j<len{if a[j]==candidate{return true;}j+=1;}false
}
fn owned_step(mut a:[u32;22],mut len:usize,mut draws:usize,candidate:u32)->([u32;22],usize,usize,bool){
 if len==22 || draws==64{return(a,len,draws,true);}
 draws+=1;
 if !owned_contains(&a,len,candidate){a[len]=candidate;len+=1;}
 (a,len,draws,false)
}
#[cfg(kani)]mod proofs{
 use super::*;
 fn word_value_equal<const N:usize>(){
  let a=kani::any::<[u32;22]>();let n=N;let d=kani::any::<usize>();let b=kani::any::<u32>();
  assert!(N<=22);kani::assume(d<=64);
  let (x,n1,d1,s1)=aspis_core::r0_transcript::s126_scan_step(a,n,d,b);
  let (y,n2,d2,s2)=owned_step(a,n,d,b);
  assert!(n1==n2);assert!(d1==d2);assert!(s1==s2);
  let mut i=0;while i<22{assert!(x[i]==y[i]);i+=1;}
  assert!(n1<=22);assert!(d1<=64);
  kani::cover!(s1,"stopped");kani::cover!(!s1,"complete block");
 }
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_0(){word_value_equal::<0>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_1(){word_value_equal::<1>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_2(){word_value_equal::<2>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_3(){word_value_equal::<3>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_4(){word_value_equal::<4>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_5(){word_value_equal::<5>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_6(){word_value_equal::<6>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_7(){word_value_equal::<7>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_8(){word_value_equal::<8>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_9(){word_value_equal::<9>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_10(){word_value_equal::<10>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_11(){word_value_equal::<11>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_12(){word_value_equal::<12>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_13(){word_value_equal::<13>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_14(){word_value_equal::<14>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_15(){word_value_equal::<15>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_16(){word_value_equal::<16>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_17(){word_value_equal::<17>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_18(){word_value_equal::<18>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_19(){word_value_equal::<19>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_20(){word_value_equal::<20>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_21(){word_value_equal::<21>();}
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal_22(){word_value_equal::<22>();}
}
