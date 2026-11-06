use super::*;
use aspis_core::field::{M31,CM31};
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn word(bytes:&[u8],at:usize)->u32{u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]])}
fn kw(q:K)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn check(){let bytes:[u8;160]=kani::any();
 let good=word(&bytes,0)<2147483647&&word(&bytes,4)<2147483647&&word(&bytes,8)<2147483647&&word(&bytes,12)<2147483647&&word(&bytes,16)<2147483647&&word(&bytes,20)<2147483647&&word(&bytes,24)<2147483647&&word(&bytes,28)<2147483647&&word(&bytes,32)<2147483647&&word(&bytes,36)<2147483647&&word(&bytes,40)<2147483647&&word(&bytes,44)<2147483647&&word(&bytes,48)<2147483647&&word(&bytes,52)<2147483647&&word(&bytes,56)<2147483647&&word(&bytes,60)<2147483647&&word(&bytes,64)<2147483647&&word(&bytes,68)<2147483647&&word(&bytes,72)<2147483647&&word(&bytes,76)<2147483647&&word(&bytes,80)<2147483647&&word(&bytes,84)<2147483647&&word(&bytes,88)<2147483647&&word(&bytes,92)<2147483647&&word(&bytes,96)<2147483647&&word(&bytes,100)<2147483647&&word(&bytes,104)<2147483647&&word(&bytes,108)<2147483647&&word(&bytes,112)<2147483647&&word(&bytes,116)<2147483647&&word(&bytes,120)<2147483647&&word(&bytes,124)<2147483647&&word(&bytes,128)<2147483647&&word(&bytes,132)<2147483647&&word(&bytes,136)<2147483647&&word(&bytes,140)<2147483647&&word(&bytes,144)<2147483647&&word(&bytes,148)<2147483647&&word(&bytes,152)<2147483647&&word(&bytes,156)<2147483647;
 let result=read_checkpoint_semantic_alpha(&bytes,0);
 assert_eq!(result.is_ok(),good^cfg!(NJC_invert));
 match result{Ok((out,at))=>{assert_eq!(at,160);
assert_eq!(kw(out[0]),[word(&bytes,0),word(&bytes,4),word(&bytes,8),word(&bytes,12)]);
assert_eq!(kw(out[1]),[word(&bytes,16),word(&bytes,20),word(&bytes,24),word(&bytes,28)]);
assert_eq!(kw(out[2]),[word(&bytes,32),word(&bytes,36),word(&bytes,40),word(&bytes,44)]);
assert_eq!(kw(out[3]),[word(&bytes,48),word(&bytes,52),word(&bytes,56),word(&bytes,60)]);
assert_eq!(kw(out[4]),[word(&bytes,64),word(&bytes,68),word(&bytes,72),word(&bytes,76)]);
assert_eq!(kw(out[5]),[word(&bytes,80),word(&bytes,84),word(&bytes,88),word(&bytes,92)]);
assert_eq!(kw(out[6]),[word(&bytes,96),word(&bytes,100),word(&bytes,104),word(&bytes,108)]);
assert_eq!(kw(out[7]),[word(&bytes,112),word(&bytes,116),word(&bytes,120),word(&bytes,124)]);
assert_eq!(kw(out[8]),[word(&bytes,128),word(&bytes,132),word(&bytes,136),word(&bytes,140)]);
assert_eq!(kw(out[9]),[word(&bytes,144),word(&bytes,148),word(&bytes,152),word(&bytes,156)]);
},Err(error)=>assert_eq!(error,Error::Checkpoint)}
}
#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic(){check();}
#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_renamed(){check();}
