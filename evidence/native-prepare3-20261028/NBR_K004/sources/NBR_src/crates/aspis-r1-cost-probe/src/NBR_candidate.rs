use super::*;
#[derive(Clone,Copy)] struct NBR_Digest;
impl Digest32 for NBR_Digest{fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"no digest before prepare cut");[0;32]}}
static mut NBR_BASE:*const u8=core::ptr::null();
static mut NBR_SCANNED:bool=false;
static mut NBR_ACCEPT:bool=false;
fn NBR_scan(proof:&[u8])->Result<(),Error>{unsafe{
 assert_eq!(proof.as_ptr(),NBR_BASE);assert_eq!(proof.len(),57607);NBR_SCANNED=NBR_ACCEPT;
 if NBR_ACCEPT{Ok(())}else{Err(Error::Parse)}
}}
fn NBR_prepare_cut<H:Digest32>(_:Public<'_>,proof:&[u8],_:H,obs:Observer,g:&mut[E;29])->Result<Box<Prepared>,Error>{unsafe{
 assert!(NBR_SCANNED);assert_eq!(proof.as_ptr(),NBR_BASE);assert_eq!(proof.len(),57607);assert!(obs.is_none());
 let i:usize=kani::any();kani::assume(i<29);assert_eq!(g[i],E::ZERO);
 kani::cover!(true,"prepare is reached with successful scan on SAME full stored proof");kani::assume(false);Err(Error::Parse)
}}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(crate::verifier::candidate::canonical_scan,NBR_scan)]
#[kani::stub(crate::verifier::candidate::prepare::<NBR_Digest>,NBR_prepare_cut)]
fn NBR_tx1_prepare_cut(){
 let mut backing:[u8;57607]=kani::any();
 // The header stays arbitrary; the cover witnesses its genuine accepted arm.
 let n:usize=kani::any();kani::assume(n<=57607);
 let p:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};
 let t:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};
 unsafe{NBR_BASE=backing.as_ptr();NBR_SCANNED=false;NBR_ACCEPT=kani::any();}
 let r=tx1(Public::Transfer(&p,&t),&[],&backing[..n],10,NBR_Digest,None);
 match r{Err(e)=>assert_eq!(e,Error::Parse),Ok(_)=>assert!(false,"prepare cut stops all successful paths")};
 kani::cover!(n<57607,"short proof rejects before prepare");
}
