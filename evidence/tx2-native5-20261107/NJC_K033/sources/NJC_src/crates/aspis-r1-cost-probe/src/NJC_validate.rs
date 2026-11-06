use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct Contains<'a>{queries:&'a[u32;22],i:usize,answer:bool,calls:usize}
impl Contains<'_>{fn contains(&mut self,prefix:&[u32],q:&u32)->bool{
 assert_eq!(prefix.as_ptr(),self.queries.as_ptr());assert_eq!(prefix.len(),self.i);assert_eq!(*q,self.queries[self.i]);self.calls+=1;self.answer
}}
// Literal one entered outer iteration; contains is the entered child cut.
fn step(queries:&[u32;22],i:usize,log:&mut Contains)->Result<usize,Error>{
 let q=queries[i];
 if q>=1<<18||log.contains(&queries[..i],&q){return Err(Error::Checkpoint);}
 Ok(i+1)
}
fn check(){let queries:[u32;22]=kani::any();let i:usize=kani::any();kani::assume(i<22);let answer:bool=kani::any();let mut log=Contains{queries:&queries,i,answer,calls:0};
 let result=step(&queries,i,&mut log);let bad=queries[i]>=262144||answer;
 assert_eq!(result.is_err(),bad^cfg!(NJC_invert));
 match result{Ok(next)=>assert_eq!(next,i+1),Err(e)=>assert_eq!(e,Error::Checkpoint)}
 assert_eq!(log.calls,if queries[i]>=262144{0}else{1});
}
#[kani::proof]
#[kani::unwind(26)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn validate_step(){check();}
#[kani::proof]
#[kani::unwind(26)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn validate_step_renamed(){check();}
