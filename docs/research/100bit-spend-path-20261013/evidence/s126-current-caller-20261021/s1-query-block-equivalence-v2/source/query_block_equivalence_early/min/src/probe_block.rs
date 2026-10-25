#![no_std]
extern crate alloc;
fn owned_block(mut accepted:[u32;22],mut len:usize,mut draws:usize,block:&[u8;32])->([u32;22],usize,usize,bool){
 let mut i=0;
 while i<8{
  if len==22 || draws==64{return(accepted,len,draws,true);}
  let off=4*i;let candidate=u32::from_le_bytes([block[off],block[off+1],block[off+2],block[off+3]])&((1u32<<18)-1);
  draws+=1;let mut j=0;let mut found=false;
  while j<len{if accepted[j]==candidate{found=true;break;}j+=1;}
  if !found{accepted[len]=candidate;len+=1;}
  i+=1;
 }
 (accepted,len,draws,false)
}
#[cfg(kani)]mod proofs{
 use super::*;
 #[kani::proof]#[kani::unwind(24)]fn block_value_equal(){
  let a=kani::any::<[u32;22]>();let n=kani::any::<usize>();let d=kani::any::<usize>();let b=kani::any::<[u8;32]>();
  kani::assume(n<=22);kani::assume(d<=64);
  let (x,n1,d1,s1)=aspis_core::r0_transcript::s126_scan_block(a,n,d,&b);
  let (y,n2,d2,s2)=owned_block(a,n,d,&b);
  assert!(n1==n2);assert!(d1==d2);assert!(s1==s2);
  let mut i=0;while i<22{assert!(x[i]==y[i]);i+=1;}
  assert!(n1<=22);assert!(d1<=64);
  kani::cover!(s1,"stopped");kani::cover!(!s1,"complete block");
 }
}
