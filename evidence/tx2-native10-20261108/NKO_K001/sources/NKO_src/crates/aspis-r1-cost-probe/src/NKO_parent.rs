//! NKO C03 exact tx2_common inactive call window; children are local oracles.
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct InactiveLog<'a>{proof:&'a[u8],reply:Option<E>,calls:usize}
impl InactiveLog<'_>{fn decode(&mut self,bytes:&[u8])->Option<E>{
 self.calls+=1;
 assert_eq!(bytes.as_ptr(),self.proof.as_ptr().wrapping_add(7495));
 assert_eq!(bytes.len(),32);
 let i=(kani::any::<u8>()&31) as usize;
 assert_eq!(bytes[i],self.proof[7495+i]^(if cfg!(NKO_invert){1}else{0}));
 self.reply
}}
// Literal source window: constants and ? are unchanged; only child is logged.
fn inactive_stage(proof:&[u8],log:&mut InactiveLog)->Result<E,Error>{
 let inactive=log.decode(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
 Ok(inactive)
}
fn any_e()->E{let w:[u32;8]=kani::any();E::new(K::new(w[0],w[1],w[2],w[3]),K::new(w[4],w[5],w[6],w[7]))}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn inactive_call(){
 let bytes:[u8;57607]=kani::any();let len:usize=kani::any();kani::assume(7527<=len&&len<=57607);
 let proof=&bytes[..len];let reply=if kani::any(){Some(any_e())}else{None};
 let mut log=InactiveLog{proof,reply,calls:0};let out=inactive_stage(proof,&mut log);
 assert_eq!(log.calls,1);assert_eq!(out,reply.ok_or(Error::Parse));
 let j:usize=kani::any();kani::assume(j<len);assert_eq!(proof[j],bytes[j]);
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn inactive_short_no_return(){
 let bytes:[u8;7527]=kani::any();let len:usize=kani::any();kani::assume(len<7527);
 let proof=if cfg!(NKO_invert){&bytes[..]}else{&bytes[..len]};
 let mut log=InactiveLog{proof,reply:None,calls:0};let _=inactive_stage(proof,&mut log);
 assert!(false,"NKO short slice continuation is unreachable");
}
