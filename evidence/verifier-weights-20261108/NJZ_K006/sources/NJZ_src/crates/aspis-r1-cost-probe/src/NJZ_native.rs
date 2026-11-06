use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(b:&[u8],i:usize)->u32 {u32::from_le_bytes([b[i],b[i+1],b[i+2],b[i+3]])}
// Actual frozen echeck, at most ONE complete chunk; arbitrary trailing bytes.
// The unbounded composition uses NJJ_Chunks and Lean first-error induction.
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn echeck_window(){
 let bytes:[u8;63]=kani::any();let n:usize=kani::any();kani::assume(n<=63);let k:bool=kani::any();
 let result=echeck(&bytes[..n],k);
 let mut good=true;
 if n>=32 {
  let words=[word(&bytes,0),word(&bytes,4),word(&bytes,8),word(&bytes,12),word(&bytes,16),word(&bytes,20),word(&bytes,24),word(&bytes,28)];
  for w in words {good=good&&w<2147483647;}
  if k {good=good&&words[4]==0&&words[5]==0&&words[6]==0&&words[7]==0;}
 }
 let expected=if good {Ok(())}else{Err(Error::Parse)};
 assert_eq!(result.is_ok(),expected.is_ok()^cfg!(NJZ_invert));
 if result.is_err(){assert_eq!(result,Err(Error::Parse));}
}

fn qm(words:[u32;4])->K {K{c0:aspis_core::field::CM31{a:M31(words[0]),b:M31(words[1])},c1:aspis_core::field::CM31{a:M31(words[2]),b:M31(words[3])}}}
struct ParseLog<'a>{expected:&'a[u8],reply:Option<E>,calls:usize}
impl ParseLog<'_>{fn parse(&mut self,c:&[u8])->Option<E>{
 assert_eq!(c.as_ptr(),self.expected.as_ptr());assert_eq!(c.len(),32);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(c[j],self.expected[j]);
 self.calls+=1;self.reply
}}
// Literal one-iteration echeck body; only its CLOSED parser call is a local oracle.
fn echeck_cut(c:&[u8],k:bool,log:&mut ParseLog)->Result<(),Error>{
 let x=log.parse(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO{return Err(Error::Parse);} Ok(())
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn echeck_step(){
 let bytes:[u8;32]=kani::any();let low:[u32;4]=kani::any();let high:[u32;4]=kani::any();let some:bool=kani::any();let k:bool=kani::any();
 for w in low{kani::assume(w<2147483647);}for w in high{kani::assume(w<2147483647);}
 let reply=if some{Some(E::new(qm(low),qm(high)))}else{None};
 let mut log=ParseLog{expected:&bytes,reply,calls:0};let out=echeck_cut(&bytes,k,&mut log);
 let good=some&&(!k||high==[0;4]);assert_eq!(out.is_ok(),good^cfg!(NJZ_invert));
 if !good{assert_eq!(out,Err(Error::Parse));}assert_eq!(log.calls,1);assert_eq!(log.reply,reply);
}
