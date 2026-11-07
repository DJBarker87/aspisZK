//! Claims-error partition on ACTUAL verify_finish. One arbitrary argument window.
use super::*;
use crate::r1_wire::NMO_wire as W;
use core::cell::RefCell;
use aspis_core::field::{M31,CM31};
use aspis_statement::pool_v1::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct NMO_State { window:usize,rounds:usize,claims:usize,round_ptr:usize,round_len:usize,claim_ptr:usize,claim_len:usize,
 state:[u8;32],next:u8,reply:[u8;32],frame:[u64;4],mid:[u64;4],after:[u64;4],omit:bool }
#[derive(Clone,Copy)]
struct NMO_Hash<'a>(&'a RefCell<NMO_State>);
#[repr(C)]
struct NMO_Carrier {root:[u8;32],log:RefCell<NMO_State>}
impl Digest32 for NMO_Hash<'_>{
 fn digest(&self,parts:&[&[u8]])->[u8;32]{
  let mut l=self.0.borrow_mut();l.rounds+=1;let w=l.window;
  l.round_ptr=parts[w].as_ptr() as usize;l.round_len=parts[w].len();
  for i in 0..32{l.state[i]=parts[28][i];}l.next=parts[29][0];
  l.frame=l.mid;l.reply
 }
}
fn NMO_q()->QM31{let a:[u32;4]=kani::any();QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}}}
fn NMO_digest()->[M31;8]{core::array::from_fn(|_|M31(kani::any()))}
fn NMO_error(b:[u8;32])->Error{
 let v=usize::from_le_bytes([b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11]]);
 match b[0]{0=>Error::Allocation,1=>Error::RowOrder{expected:b[1],actual:b[2]},2=>Error::InvalidRow,
 3=>Error::Tag{row:b[1]},4=>Error::Length{row:b[1]},5=>Error::NonCanonical{row:b[1],value:v},
 6=>Error::Boundary{round:v},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}
}
fn NMO_rounds_ok<H:Digest32>(p:&Prefix<'_>,t:SemanticTranscript<H>)->Result<(QM31,[QM31;10],SemanticTranscript<H>),Error>{
 let state=t.state();let next=[t.next_row()];let parts:[&[u8];30]=[
p.c1_root,
W::record(p,0),
W::record(p,1),
W::record(p,2),
W::record(p,3),
W::record(p,4),
W::record(p,5),
W::record(p,6),
W::record(p,7),
W::record(p,8),
W::record(p,9),
W::record(p,10),
W::record(p,11),
W::record(p,12),
W::record(p,13),
W::record(p,14),
W::record(p,15),
W::record(p,16),
W::record(p,17),
W::record(p,18),
W::record(p,19),
W::record(p,20),
W::record(p,21),
W::record(p,22),
W::record(p,23),
W::record(p,24),
W::record(p,25),
W::record(p,26),
&state,&next];
W::hash(&t).digest(&parts);
let (_,hash,_)=W::into_parts(t);
Ok((NMO_q(),core::array::from_fn(|_|NMO_q()),W::make(hash,kani::any(),kani::any())))
}
fn NMO_claims_err(p:&Prefix<'_>)->Result<Box<[[QM31;29];3]>,Error>{
 // Existing Prefix data channel, disjoint root and RefCell fields of one allocation.
 let carrier=unsafe{&*(p.c1_root.as_ptr() as *const NMO_Carrier)};
 let mut l=carrier.log.borrow_mut();l.claims+=1;
 let bytes=if l.window==0{&p.c1_root[..]}else{W::record(p,l.window-1)};
 l.claim_ptr=bytes.as_ptr() as usize;l.claim_len=bytes.len();let after=l.after;
 l.frame[0]=after[0];l.frame[1]=after[1];l.frame[2]=after[2];if !l.omit{l.frame[3]=after[3];}
 Err(NMO_error(l.reply))
}
fn NMO_parent<const IGNORE:bool,const ARG:bool,const OMIT:bool>(){
 let window:usize=kani::any();kani::assume(window<28);let reply:[u8;32]=kani::any();kani::assume(reply[0]<11);
 let seed=NMO_State{window,rounds:0,claims:0,round_ptr:0,round_len:0,claim_ptr:0,claim_len:0,state:[0;32],next:0,reply,frame:kani::any(),mid:kani::any(),after:kani::any(),omit:OMIT};
 let carrier=NMO_Carrier{root:kani::any(),log:RefCell::new(seed)};
 let proof:[u8;57575]=kani::any();let lens:[usize;27]=kani::any();
 let records=core::array::from_fn(|i|{kani::assume(lens[i]<=57575);&proof[..lens[i]]});
 let prefix=W::prefix(&carrier.root,records);
 let expected=if window==0{&prefix.c1_root[..]}else{W::record(&prefix,window-1)};
 let state:[u8;32]=kani::any();let next:u8=kani::any();
 let supplied=if ARG{let mut altered=state;altered[0]^=1;altered}else{state};
 let transcript=W::make(NMO_Hash(&carrier.log),supplied,next);
 let transfer=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NMO_digest(),nullifier:NMO_digest(),asset_id:M31(kani::any()),recipient_commitment:NMO_digest(),change_commitment:NMO_digest()};
 let withdrawal=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NMO_digest(),nullifier:NMO_digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:NMO_digest()};
 let transition=PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:NMO_digest(),frontier:core::array::from_fn(|_|NMO_digest())},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:NMO_digest(),next_frontier:core::array::from_fn(|_|NMO_digest())}};
 let public=if kani::any(){Public::Transfer(&transfer,&transition)}else{Public::Withdrawal(&withdrawal,&transition)};
 let challenges=Challenges{lambda:NMO_q(),chi:NMO_q(),theta:NMO_q(),zc:core::array::from_fn(|_|NMO_q()),mu:NMO_q(),eta:NMO_q()};
 let result=verify_finish(public,prefix,transcript,challenges,None);
 let post=*carrier.log.borrow();
 assert_eq!(post.rounds,1);assert_eq!(post.claims,1);
 assert_eq!(post.round_ptr,expected.as_ptr() as usize);assert_eq!(post.round_len,expected.len());
 assert_eq!(post.claim_ptr,expected.as_ptr() as usize);assert_eq!(post.claim_len,expected.len());
 assert_eq!(post.state,state);assert_eq!(post.next,next);
 let error=if IGNORE{Error::Public}else{NMO_error(reply)};
 match result{Err(e)=>assert_eq!(e,error),Ok(_)=>assert!(false,"claims Err must propagate")}
 assert_eq!(post.frame,seed.after,"complete reachable carrier write window");
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_claims_error(){NMO_parent::<false,false,false>();}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_claims_reply_control(){NMO_parent::<true,false,false>();}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_claims_argument_control(){NMO_parent::<false,true,false>();}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_claims_footprint_control(){NMO_parent::<false,false,true>();}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_claims_error_stability(){NMO_parent::<false,false,false>();}
