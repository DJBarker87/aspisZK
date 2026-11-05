use super::*;
use aspis_statement::pool_v1::{pair_forest_semantic_terminal::r0::Public,payment_relation::{PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1},pair_tree_profile::PoolV1PairLatePublicStatementV1};
use aspis_core::field::M31;
type Digest=[M31;8];
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]struct Hash(u64);
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("oracle only")}}
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
fn public_id(p:Public<'_>)->(bool,*const u8,*const PoolV1PairLatePublicStatementV1){match p{Public::Transfer(a,t)=>(false,a as *const _ as *const u8,t),Public::Withdrawal(a,t)=>(true,a as *const _ as *const u8,t)}}
struct Log{produced:Option<Result<Vec<u8>,Error>>,constructor_error:Option<Error>,state:[u8;32],cursor:u8,producer_calls:usize,new_calls:usize,public_id:(bool,*const u8,*const PoolV1PairLatePublicStatementV1),observe:usize,byte:u8,ptr:*const u8,length:usize,hash:u64,root:*const u8,root_byte:u8,root_index:usize}
fn NHG_producer_cut(public:Public<'_>,log:&mut Log)->Result<Vec<u8>,Error>{log.producer_calls+=1;log.public_id=public_id(public);log.produced.take().unwrap()}
fn NHG_new_cut(hash:Hash,bytes:&[u8],root:&[u8;32],log:&mut Log)->Result<SemanticTranscript<Hash>,Error>{
 log.new_calls+=1;log.ptr=bytes.as_ptr();log.length=bytes.len();log.byte=if log.observe<bytes.len(){bytes[log.observe]}else{0};log.hash=hash.0;log.root=root.as_ptr();log.root_byte=root[log.root_index];
 match log.constructor_error{Some(e)=>Err(e),None=>Ok(SemanticTranscript{state:log.state,hash,next_row:log.cursor})}
}
fn NHG_public_control(public:Public<'_>,hash:Hash,c1_root:&[u8;32],log:&mut Log)->Result<SemanticTranscript<Hash>,Error>{

    NHG_new_cut(
        hash,
        &NHG_producer_cut(public,log).map_err(|_| Error::Public)?,
        c1_root,log,
    )

}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_public_carrier(){
 let p=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()};
 let w=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()};
 // Fully arbitrary typed transition: no zero/sparse prestate restriction.
 let t=PoolV1PairLatePublicStatementV1{
  live_snapshot:aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{
   pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:core::array::from_fn(|_|digest())},
  candidate_afterstate:aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1{
   next_pair_index:kani::any(),next_root:digest(),next_frontier:core::array::from_fn(|_|digest())}};
 let withdrawal:bool=kani::any();let public=if withdrawal{Public::Withdrawal(&w,&t)}else{Public::Transfer(&p,&t)};

 let n:usize=kani::any();kani::assume(n<=1455);let mut bytes=kani::vec::exact_vec::<u8,1455>();bytes.truncate(n);let pointer=bytes.as_ptr();let observe:usize=kani::any();kani::assume(observe<1455);let byte=if observe<n{bytes[observe]}else{0};
 let producer_fail:bool=kani::any();let constructor_fail:bool=kani::any();let error=any_error();let producer_error=any_error();let hash:u64=kani::any();let root:[u8;32]=kani::any();let state:[u8;32]=kani::any();let cursor:u8=kani::any();let index:usize=kani::any();kani::assume(index<32);
 let mut log=Log{produced:Some(if producer_fail{Err(producer_error)}else{Ok(bytes)}),constructor_error:if constructor_fail{Some(error)}else{None},state,cursor,producer_calls:0,new_calls:0,public_id:(false,core::ptr::null(),core::ptr::null()),observe,byte:0,ptr:core::ptr::null(),length:0,hash:0,root:core::ptr::null(),root_byte:0,root_index:index};
 let got=NHG_public_control(public,Hash(hash),&root,&mut log);
 assert_eq!(log.producer_calls,1);assert_eq!(log.public_id,public_id(public));assert_eq!(log.new_calls,if producer_fail{0}else{1});
 if cfg!(NHG_invert){kani::assume(!producer_fail&&observe<n);}
 if producer_fail{assert!(matches!(got,Err(Error::Public)));}else{
  assert_eq!(log.ptr,pointer);assert_eq!(log.length,n);if observe<n{assert_eq!(log.byte,byte^if cfg!(NHG_invert){1}else{0});}
  assert_eq!(log.hash,hash);assert_eq!(log.root,root.as_ptr());assert_eq!(log.root_byte,root[index]);
  match got{Err(e)=>{assert!(constructor_fail);assert_eq!(e,error)},Ok(t)=>{assert!(!constructor_fail);assert_eq!(t.hash.0,hash);assert_eq!(t.next_row,cursor);assert_eq!(t.state[index],state[index]);}}
 }
}
