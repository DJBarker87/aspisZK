use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use crate::r1_wire as wire;
use wire::NCH_wire as carrier;
#[derive(Clone,Copy)]struct NCH_Digest(u64);
impl Digest32 for NCH_Digest{fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"digest belongs to the cut child");[0;32]}}
static mut NCH_MODE:u8=0;static mut NCH_STAGE:u8=0;static mut NCH_INDEX:usize=0;
static mut NCH_BYTES:*const u8=core::ptr::null();static mut NCH_P:*const u8=core::ptr::null();static mut NCH_T:*const u8=core::ptr::null();
static mut NCH_STATES:[[u8;32];3]=[[0;32];3];static mut NCH_HASH:u64=0;static mut NCH_CALLBACKS:usize=0;
static mut NCH_CH:wire::Challenges=wire::Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:[K::ZERO;10],mu:K::ZERO,eta:K::ZERO};
static mut NCH_ROOTS:[[u8;32];2]=[[0;32];2];static mut NCH_ALPHA:[K;10]=[K::ZERO;10];static mut NCH_CLAIMS:[[K;29];3]=[[K::ZERO;29];3];static mut NCH_EXTRA:[K;29]=[K::ZERO;29];static mut NCH_BEFORE:[K;29]=[K::ZERO;29];static mut NCH_BEFORE_STATE:[u8;32]=[0;32];static mut NCH_Z:[SecureCirclePoint;2]=[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2];static mut NCH_CLAIM_PTR:*const K=core::ptr::null();
fn NCH_public_identity(public:Public<'_>){unsafe{match public{Public::Transfer(p,t)=>{assert_eq!(p as *const _ as *const u8,NCH_P);assert_eq!(t as *const _ as *const u8,NCH_T);},_=>assert!(false,"same public variant")}}}
struct NCH_Parser<'a>(core::marker::PhantomData<&'a ()>);
impl<'a> NCH_Parser<'a>{fn parse(bytes:&'a[u8])->Result<wire::Prefix<'a>,wire::Error>{unsafe{
 assert_eq!(NCH_STAGE,0);assert_eq!(bytes.as_ptr(),NCH_BYTES);assert_eq!(bytes.len(),13831);NCH_STAGE=1;
 if NCH_MODE==0{return Err(wire::Error::Length{row:0});}
 let root:&[u8;32]=bytes[..32].try_into().unwrap();
 let records=[&bytes[32..37],&bytes[37..42],&bytes[42..79],&bytes[79..84],&bytes[84..89],&bytes[89..94],&bytes[94..99],&bytes[99..104],&bytes[104..109],&bytes[109..114],&bytes[114..119],&bytes[119..124],&bytes[124..129],&bytes[129..134],&bytes[134..171],&bytes[171..1072],&bytes[1072..1973],&bytes[1973..2874],&bytes[2874..3775],&bytes[3775..4676],&bytes[4676..5577],&bytes[5577..6478],&bytes[6478..7379],&bytes[7379..8280],&bytes[8280..9181],&bytes[9181..12898],&bytes[12898..13831]];Ok(carrier::prefix(root,records))
}}}
fn NCH_public<H:Digest32>(public:Public<'_>,hash:H,root:&[u8;32])->Result<wire::SemanticTranscript<H>,wire::Error>{unsafe{
 assert_eq!(NCH_STAGE,1);NCH_public_identity(public);assert_eq!(root.as_ptr(),NCH_BYTES);NCH_STAGE=2;
 if NCH_MODE==1{return Err(wire::Error::Public);}
 Ok(carrier::transcript(hash,NCH_STATES[0],0))
}}
fn NCH_begin<H:Digest32>(prefix:&wire::Prefix<'_>,t:&mut wire::SemanticTranscript<H>)->Result<wire::Challenges,wire::Error>{unsafe{
 assert_eq!(NCH_STAGE,2);assert_eq!(prefix.c1_root.as_ptr(),NCH_BYTES);assert_eq!(t.state()[NCH_INDEX],NCH_STATES[0][NCH_INDEX]);assert_eq!(t.next_row(),0);NCH_STAGE=3;
 carrier::update(t,NCH_STATES[1],15);
 if NCH_MODE==2{return Err(wire::Error::RowOrder{expected:0,actual:1});}
 Ok(NCH_CH)
}}
fn NCH_finish<H:Digest32>(public:Public<'_>,prefix:wire::Prefix<'_>,t:wire::SemanticTranscript<H>,ch:wire::Challenges,obs:Observer)->Result<crate::r1_semantic::Verified<H>,wire::Error>{unsafe{
 assert_eq!(NCH_STAGE,3);NCH_public_identity(public);assert_eq!(prefix.c1_root.as_ptr(),NCH_BYTES);let _=obs; // NCH_ObserverErasure.finish/source; default feature mark is inert.
assert_eq!(t.state()[NCH_INDEX],NCH_STATES[1][NCH_INDEX]);assert_eq!(t.next_row(),15);
 assert_eq!(ch.lambda,NCH_CH.lambda);assert_eq!(ch.chi,NCH_CH.chi);assert_eq!(ch.theta,NCH_CH.theta);assert_eq!(ch.mu,NCH_CH.mu);assert_eq!(ch.eta,NCH_CH.eta);let a:usize=kani::any();kani::assume(a<10);assert_eq!(ch.zc[a],NCH_CH.zc[a]);
 NCH_STAGE=4;if NCH_MODE==3{return Err(wire::Error::Terminal);}
 let claims=Box::new(NCH_CLAIMS);NCH_CLAIM_PTR=claims.as_ptr().cast::<K>();
 Ok(crate::r1_semantic::Verified{roots:NCH_ROOTS,challenges:ch,alpha:NCH_ALPHA,claims,extra:NCH_EXTRA,before_z1:NCH_BEFORE,state_before_z0:NCH_BEFORE_STATE,z:NCH_Z,transcript:carrier::transcript(carrier::into_hash(t),NCH_STATES[2],27)})
}}
fn NCH_init(bytes:*const u8,p:*const u8,t:*const u8,mode:u8,index:usize){unsafe{
 NCH_STAGE=0;NCH_MODE=mode;NCH_INDEX=index;NCH_BYTES=bytes;NCH_P=p;NCH_T=t;NCH_HASH=kani::any();NCH_STATES=kani::any();NCH_CALLBACKS=0;
 NCH_CH=wire::Challenges{lambda:core::mem::transmute::<[u8;16],K>(kani::any()),chi:core::mem::transmute::<[u8;16],K>(kani::any()),theta:core::mem::transmute::<[u8;16],K>(kani::any()),zc:core::mem::transmute::<[u8;160],[K;10]>(kani::any()),mu:core::mem::transmute::<[u8;16],K>(kani::any()),eta:core::mem::transmute::<[u8;16],K>(kani::any())};
 // Finish-error split never reads successful Verified fields.
}}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(crate::r1_wire::Prefix::parse,NCH_Parser::parse)]
#[kani::stub(crate::r1_semantic::public_transcript,NCH_public)]
#[kani::stub(crate::r1_wire::begin,NCH_begin)]
#[kani::stub(crate::r1_semantic::verify_finish,NCH_finish)]
fn NCH_observed_finish_error(){
 let p:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};let t:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};let bytes:[u8;13831]=kani::any();let index:usize=kani::any();kani::assume(index<32);
 NCH_init(bytes.as_ptr(),&p as *const _ as *const u8,&t as *const _ as *const u8,3,index);
 let result=crate::r1_semantic::verify_observed(Public::Transfer(&p,&t),&bytes,unsafe{NCH_Digest(NCH_HASH)},None);
 assert!(matches!(result,Err(wire::Error::Terminal)));unsafe{assert_eq!(NCH_STAGE,4);}
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(crate::r1_wire::Prefix::parse,NCH_Parser::parse)]
#[kani::stub(crate::r1_semantic::public_transcript,NCH_public)]
#[kani::stub(crate::r1_wire::begin,NCH_begin)]
#[kani::stub(crate::r1_semantic::verify_finish,NCH_finish)]
fn NCH_observed_finish_error_wrong(){
 let p:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};let t:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};let bytes:[u8;13831]=kani::any();let index:usize=kani::any();kani::assume(index<32);
 NCH_init(bytes.as_ptr(),&p as *const _ as *const u8,&t as *const _ as *const u8,3,index);
 let result=crate::r1_semantic::verify_observed(Public::Transfer(&p,&t),&bytes,unsafe{NCH_Digest(NCH_HASH)},None);
 assert!(matches!(result,Err(wire::Error::Public)),"wrong returned finish error");
}
