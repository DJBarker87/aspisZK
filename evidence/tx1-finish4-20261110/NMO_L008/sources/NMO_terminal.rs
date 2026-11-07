//! Terminal-Err partition on ACTUAL frozen verify_finish; one arbitrary scalar/argument window.
use super::*;
use crate::r1_wire::NMO_wire as W;
use core::cell::RefCell;
use aspis_core::field::{M31,CM31};
use aspis_statement::pool_v1::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct NMO_State { window:usize,rounds:usize,claims:usize,round_ptr:usize,round_len:usize,claim_ptr:usize,claim_len:usize,
 state:[u8;32],next:u8,reply:[u8;32],frame:[u64;4],mid:[u64;4],after:[u64;4],omit:bool, ci:usize,cj:usize,channel:usize,expected_alpha:u32,expected_claim:u32,claim_owner:usize,terminal_calls:usize,seen_alpha:u32,seen_claim:u32,seen_ch:u32,public_ptr:usize,transition_ptr:usize,variant:bool }
#[derive(Clone,Copy)]
struct NMO_Hash<'a>(&'a RefCell<NMO_State>);
#[repr(C)]
struct NMO_Carrier {root:[u8;32],log:RefCell<NMO_State>}
impl Digest32 for NMO_Hash<'_>{
 fn digest(&self,parts:&[&[u8]])->[u8;32]{
  let mut l=self.0.borrow_mut();l.rounds+=1;let w=l.window;
  l.round_ptr=parts[w].as_ptr() as usize;l.round_len=parts[w].len();
  for i in 0..32{l.state[i]=parts[28][i];}l.next=parts[29][0];
  let offset=(l.ci%10*4+l.cj)*4;l.expected_alpha=u32::from_le_bytes([parts[30][offset],parts[30][offset+1],parts[30][offset+2],parts[30][offset+3]]);
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
 let state=t.state();let next=[t.next_row()];let alpha=core::array::from_fn(|_|NMO_q());
 let words:[[u32;4];10]=alpha.map(|q|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]);
 let bytes=unsafe{core::slice::from_raw_parts(words.as_ptr().cast::<u8>(),160)};let parts:[&[u8];31]=[
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
&state,&next,bytes];
W::hash(&t).digest(&parts);
let (_,hash,_)=W::into_parts(t);
Ok((NMO_q(),alpha,W::make(hash,kani::any(),kani::any())))
}
fn NMO_word(q:QM31,j:usize)->u32{match j{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn NMO_claims_ok(p:&Prefix<'_>)->Result<Box<[[QM31;29];3]>,Error>{
 let carrier=unsafe{&*(p.c1_root.as_ptr() as *const NMO_Carrier)};
 let claims=Box::new(core::array::from_fn(|_|core::array::from_fn(|_|NMO_q())));
 let mut l=carrier.log.borrow_mut();l.claims+=1;
 let bytes=if l.window==0{&p.c1_root[..]}else{W::record(p,l.window-1)};
 l.claim_ptr=bytes.as_ptr() as usize;l.claim_len=bytes.len();
 l.expected_claim=NMO_word(claims[l.ci/29][l.ci%29],l.cj);l.claim_owner=(&*claims as *const [[QM31;29];3])as usize;
 Ok(claims)
}
type NMO_PublicError=aspis_core::state_only_prefix::r0::Error;
fn NMO_pub_error(b:[u8;32])->NMO_PublicError{
 let v=usize::from_le_bytes([b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11]]);
 match b[0]{0=>NMO_PublicError::Allocation,1=>NMO_PublicError::RowOrder{expected:b[1],actual:b[2]},2=>NMO_PublicError::InvalidRow,
 3=>NMO_PublicError::Tag{row:b[1]},4=>NMO_PublicError::Length{row:b[1]},5=>NMO_PublicError::NonCanonical{row:b[1],value:v},
 6=>NMO_PublicError::Boundary{round:v},7=>NMO_PublicError::Terminal,8=>NMO_PublicError::EqualCirclePoints,9=>NMO_PublicError::TrailingBytes,_=>NMO_PublicError::Public}
}
#[repr(C)]
struct NMO_PublicCarrier<'a>{transition:PoolV1PairLatePublicStatementV1,log:&'a RefCell<NMO_State>}
fn NMO_ch(c:&aspis_core::state_only_prefix::r0::Challenges,k:usize)->QM31{
 match k{0=>c.lambda,1=>c.chi,2=>c.theta,3=>c.mu,4=>c.eta,_=>c.zc[k-5]}
}
fn NMO_terminal_err<'a>(public:Public<'a>,claims:&[[QM31;29];3],alpha:&[QM31;10],ch:&aspis_core::state_only_prefix::r0::Challenges)->Result<QM31,NMO_PublicError>{
 let (variant,first,t)=match public{Public::Transfer(p,t)=>(false,p as *const _ as usize,t),Public::Withdrawal(p,t)=>(true,p as *const _ as usize,t)};
 let carrier=unsafe{&*(t as *const PoolV1PairLatePublicStatementV1 as *const NMO_PublicCarrier<'_>)};
 let mut l=carrier.log.borrow_mut();l.terminal_calls+=1;l.public_ptr=first;l.transition_ptr=t as *const _ as usize;l.variant=variant;
 assert_eq!(claims as *const [[QM31;29];3] as usize,l.claim_owner,"SAME returned owned allocation");
 l.seen_claim=NMO_word(claims[l.ci/29][l.ci%29],l.cj);l.seen_alpha=NMO_word(alpha[l.ci%10],l.cj);l.seen_ch=NMO_word(NMO_ch(ch,l.channel),l.cj);
 let after=l.after;l.frame[0]=after[0];l.frame[1]=after[1];l.frame[2]=after[2];if !l.omit{l.frame[3]=after[3];}
 Err(NMO_pub_error(l.reply))
}
fn NMO_parent<const IGNORE:bool,const ARG:bool,const OMIT:bool>(){
 let window:usize=kani::any();kani::assume(window<28);let reply:[u8;32]=kani::any();kani::assume(reply[0]<11);
 let ci:usize=kani::any();let cj:usize=kani::any();let channel:usize=kani::any();kani::assume(ci<87&&cj<4&&channel<15);
 let seed=NMO_State{window,rounds:0,claims:0,round_ptr:0,round_len:0,claim_ptr:0,claim_len:0,state:[0;32],next:0,reply,frame:kani::any(),mid:kani::any(),after:kani::any(),omit:OMIT,ci,cj,channel,expected_alpha:0,expected_claim:0,claim_owner:0,terminal_calls:0,seen_alpha:0,seen_claim:0,seen_ch:0,public_ptr:0,transition_ptr:0,variant:false};
 let carrier=NMO_Carrier{root:kani::any(),log:RefCell::new(seed)};
 let proof:[u8;57575]=kani::any();let lens:[usize;27]=kani::any();
 let records=core::array::from_fn(|i|{kani::assume(lens[i]<=57575);&proof[..lens[i]]});
 let prefix=W::prefix(&carrier.root,records);
 let expected=if window==0{&prefix.c1_root[..]}else{W::record(&prefix,window-1)};
 let state:[u8;32]=kani::any();let next:u8=kani::any();let transcript=W::make(NMO_Hash(&carrier.log),state,next);
 let transfer=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NMO_digest(),nullifier:NMO_digest(),asset_id:M31(kani::any()),recipient_commitment:NMO_digest(),change_commitment:NMO_digest()};
 let withdrawal=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NMO_digest(),nullifier:NMO_digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:NMO_digest()};
 let transitionValue=PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:NMO_digest(),frontier:core::array::from_fn(|_|NMO_digest())},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:NMO_digest(),next_frontier:core::array::from_fn(|_|NMO_digest())}};
 let publicCarrier=NMO_PublicCarrier{transition:transitionValue,log:&carrier.log};let transition=&publicCarrier.transition;
 let choose:bool=kani::any();let public=if choose{Public::Withdrawal(&withdrawal,transition)}else{Public::Transfer(&transfer,transition)};
 let expected_public=if choose{&withdrawal as *const _ as usize}else{&transfer as *const _ as usize};
 let challenges=Challenges{lambda:NMO_q(),chi:NMO_q(),theta:NMO_q(),zc:core::array::from_fn(|_|NMO_q()),mu:NMO_q(),eta:NMO_q()};
 let mut supplied=challenges;if ARG{supplied.lambda.c0.a.0^=1;}
 let result=verify_finish(public,prefix,transcript,supplied,None);
 let post=*carrier.log.borrow();
 assert_eq!(post.rounds,1);assert_eq!(post.claims,1);assert_eq!(post.terminal_calls,1);
 assert_eq!(post.round_ptr,expected.as_ptr() as usize);assert_eq!(post.round_len,expected.len());
 assert_eq!(post.claim_ptr,expected.as_ptr() as usize);assert_eq!(post.claim_len,expected.len());
 assert_eq!(post.state,state);assert_eq!(post.next,next);
 assert_eq!(post.seen_claim,post.expected_claim);assert_eq!(post.seen_alpha,post.expected_alpha);
 assert_eq!(post.seen_ch,NMO_word(NMO_ch(&challenges,channel),cj));
 assert_eq!(post.variant,choose);assert_eq!(post.public_ptr,expected_public);assert_eq!(post.transition_ptr,transition as *const _ as usize);
 if IGNORE{assert!(result.is_ok(),"ignored terminal Err arm must not silently pass");}else{match result{Err(e)=>assert_eq!(e,Error::Public),Ok(_)=>assert!(false,"terminal Err must map to Public")}}
 assert_eq!(post.frame,seed.after,"complete reachable terminal frame");
}
#[kani::proof]#[kani::unwind(90)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_ok)]
#[kani::stub(Public::terminal_qm31,NMO_terminal_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_terminal_error(){NMO_parent::<false,false,false>();}
#[kani::proof]#[kani::unwind(90)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_ok)]
#[kani::stub(Public::terminal_qm31,NMO_terminal_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_terminal_reply_control(){NMO_parent::<true,false,false>();}
#[kani::proof]#[kani::unwind(90)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_ok)]
#[kani::stub(Public::terminal_qm31,NMO_terminal_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_terminal_argument_control(){NMO_parent::<false,true,false>();}
#[kani::proof]#[kani::unwind(90)]
#[kani::stub(semantic_rounds,NMO_rounds_ok)]#[kani::stub(claims,NMO_claims_ok)]
#[kani::stub(Public::terminal_qm31,NMO_terminal_err)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMO_terminal_footprint_control(){NMO_parent::<false,false,true>();}
