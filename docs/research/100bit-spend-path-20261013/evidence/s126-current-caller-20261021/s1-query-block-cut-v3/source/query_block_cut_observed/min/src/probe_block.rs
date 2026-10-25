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
fn owned_block(mut accepted:[u32;22],mut len:usize,mut draws:usize,block:&[u8;32])->([u32;22],usize,usize,bool){
 let mut i=0;
 while i<8{
  let off=4*i;let candidate=u32::from_le_bytes([block[off],block[off+1],block[off+2],block[off+3]])&((1u32<<18)-1);
  let (a,n,d,stop)=owned_step(accepted,len,draws,candidate);
  accepted=a;len=n;draws=d;
  if stop{return(accepted,len,draws,true);}
  i+=1;
 }
 (accepted,len,draws,false)
}
#[cfg(kani)]mod proofs{
 use super::*;
 static mut REPLIES:[bool;8]=[false;8];
 static mut CALLS:usize=0;
 static mut REF_CALLS:usize=0;
 static mut OBS_CALL:usize=0;
 static mut OBS_CELL:usize=0;
 static mut OBS_LEN:usize=0;
 static mut OBS_CANDIDATE:u32=0;
 static mut OBS_VALUE:u32=0;
 fn contains_reply<T:PartialEq+Copy+Into<u32>>(prefix:&[T],candidate:&T)->bool{unsafe{
  assert!(core::mem::size_of::<T>()==core::mem::size_of::<u32>());
  let index=CALLS;assert!(index<8);assert!(prefix.len()<22);
  if index==OBS_CALL{
   OBS_LEN=prefix.len();OBS_CANDIDATE=(*candidate).into();
   if OBS_CELL<prefix.len(){OBS_VALUE=prefix[OBS_CELL].into();}
  }
  CALLS+=1;REPLIES[index]
 }}
 fn owned_contains_reply(a:&[u32;22],len:usize,candidate:u32)->bool{unsafe{
  let index=REF_CALLS;assert!(index<CALLS);
  if index==OBS_CALL{
   assert!(len==OBS_LEN);assert!(candidate==OBS_CANDIDATE);
   if OBS_CELL<len{assert!(a[OBS_CELL]==OBS_VALUE);}
  }
  REF_CALLS+=1;REPLIES[index]
 }}
 #[kani::proof]#[kani::unwind(34)]
 #[kani::stub(<[u32]>::contains,contains_reply)]
 #[kani::stub(crate::owned_contains,owned_contains_reply)]
 fn block_cut_equal(){
  let a=kani::any::<[u32;22]>();let n=kani::any::<usize>();let d=kani::any::<usize>();let b=kani::any::<[u8;32]>();
  kani::assume(n<=22);kani::assume(d<=64);
  let observed_call=kani::any::<usize>();let observed_cell=kani::any::<usize>();
  kani::assume(observed_call<8);kani::assume(observed_cell<22);
  unsafe{REPLIES=kani::any();CALLS=0;REF_CALLS=0;OBS_CALL=observed_call;OBS_CELL=observed_cell;OBS_LEN=0;OBS_CANDIDATE=0;OBS_VALUE=0;}
  let (x,n1,d1,s1)=aspis_core::r0_transcript::s126_scan_block(a,n,d,&b);
  let (y,n2,d2,s2)=owned_block(a,n,d,&b);
  assert!(n1==n2);assert!(d1==d2);assert!(s1==s2);
  assert!(x[observed_cell]==y[observed_cell]);
  assert!(n1<=22);assert!(d1<=64);unsafe{assert!(CALLS==REF_CALLS);}
  kani::cover!(s1,"stopped");kani::cover!(!s1,"complete block");
 }
}
