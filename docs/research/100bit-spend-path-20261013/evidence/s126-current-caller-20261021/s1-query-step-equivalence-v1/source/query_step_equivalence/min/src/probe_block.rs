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
 #[kani::proof]#[kani::unwind(24)]fn word_value_equal(){
  let a=kani::any::<[u32;22]>();let n=kani::any::<usize>();let d=kani::any::<usize>();let b=kani::any::<u32>();
  kani::assume(n<=22);kani::assume(d<=64);
  let (x,n1,d1,s1)=aspis_core::r0_transcript::s126_scan_step(a,n,d,b);
  let (y,n2,d2,s2)=owned_step(a,n,d,b);
  assert!(n1==n2);assert!(d1==d2);assert!(s1==s2);
  let mut i=0;while i<22{assert!(x[i]==y[i]);i+=1;}
  assert!(n1<=22);assert!(d1<=64);
  kani::cover!(s1,"stopped");kani::cover!(!s1,"complete block");
 }
}
