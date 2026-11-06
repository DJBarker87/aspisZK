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
