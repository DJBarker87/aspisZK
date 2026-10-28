"""Native verify_observed call-structure cases, with exact typed scratch carriers.
All child replacements are overapproximations; lower source bridges stay named.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use crate::r1_wire as wire;
use wire::NCA_wire as carrier;
#[derive(Clone,Copy)]struct NCA_Digest(u64);
impl Digest32 for NCA_Digest{fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"digest belongs to the cut child");[0;32]}}
static mut NCA_MODE:u8=0;static mut NCA_STAGE:u8=0;static mut NCA_INDEX:usize=0;
static mut NCA_BYTES:*const u8=core::ptr::null();static mut NCA_P:*const u8=core::ptr::null();static mut NCA_T:*const u8=core::ptr::null();
static mut NCA_STATES:[[u8;32];3]=[[0;32];3];static mut NCA_HASH:u64=0;static mut NCA_CALLBACKS:usize=0;
static mut NCA_CH:wire::Challenges=wire::Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:[K::ZERO;10],mu:K::ZERO,eta:K::ZERO};
static mut NCA_ROOTS:[[u8;32];2]=[[0;32];2];static mut NCA_ALPHA:[K;10]=[K::ZERO;10];static mut NCA_CLAIMS:[[K;29];3]=[[K::ZERO;29];3];static mut NCA_EXTRA:[K;29]=[K::ZERO;29];static mut NCA_BEFORE:[K;29]=[K::ZERO;29];static mut NCA_BEFORE_STATE:[u8;32]=[0;32];static mut NCA_Z:[SecureCirclePoint;2]=[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2];static mut NCA_CLAIM_PTR:*const K=core::ptr::null();
fn NCA_public_identity(public:Public<'_>){unsafe{match public{Public::Transfer(p,t)=>{assert_eq!(p as *const _ as *const u8,NCA_P);assert_eq!(t as *const _ as *const u8,NCA_T);},_=>assert!(false,"same public variant")}}}
struct NCA_Parser<'a>(core::marker::PhantomData<&'a ()>);
impl<'a> NCA_Parser<'a>{fn parse(bytes:&'a[u8])->Result<wire::Prefix<'a>,wire::Error>{unsafe{
 assert_eq!(NCA_STAGE,0);assert_eq!(bytes.as_ptr(),NCA_BYTES);assert_eq!(bytes.len(),13831);NCA_STAGE=1;
 if NCA_MODE==0{return Err(wire::Error::Length{row:0});}
 let root:&[u8;32]=bytes[..32].try_into().unwrap();
 let records=[RECORDS];Ok(carrier::prefix(root,records))
}}}
fn NCA_public<H:Digest32>(public:Public<'_>,hash:H,root:&[u8;32])->Result<wire::SemanticTranscript<H>,wire::Error>{unsafe{
 assert_eq!(NCA_STAGE,1);NCA_public_identity(public);assert_eq!(root.as_ptr(),NCA_BYTES);NCA_STAGE=2;
 if NCA_MODE==1{return Err(wire::Error::Public);}
 Ok(carrier::transcript(hash,NCA_STATES[0],0))
}}
fn NCA_begin<H:Digest32>(prefix:&wire::Prefix<'_>,t:&mut wire::SemanticTranscript<H>)->Result<wire::Challenges,wire::Error>{unsafe{
 assert_eq!(NCA_STAGE,2);assert_eq!(prefix.c1_root.as_ptr(),NCA_BYTES);assert_eq!(t.state()[NCA_INDEX],NCA_STATES[0][NCA_INDEX]);assert_eq!(t.next_row(),0);NCA_STAGE=3;
 carrier::update(t,NCA_STATES[1],15);
 if NCA_MODE==2{return Err(wire::Error::RowOrder{expected:0,actual:1});}
 Ok(NCA_CH)
}}
fn NCA_finish<H:Digest32>(public:Public<'_>,prefix:wire::Prefix<'_>,t:wire::SemanticTranscript<H>,ch:wire::Challenges,obs:Observer)->Result<crate::r1_semantic::Verified<H>,wire::Error>{unsafe{
 assert_eq!(NCA_STAGE,3);NCA_public_identity(public);assert_eq!(prefix.c1_root.as_ptr(),NCA_BYTES);assert!(obs.is_none());assert_eq!(t.state()[NCA_INDEX],NCA_STATES[1][NCA_INDEX]);assert_eq!(t.next_row(),15);
 assert_eq!(ch.lambda,NCA_CH.lambda);assert_eq!(ch.chi,NCA_CH.chi);assert_eq!(ch.theta,NCA_CH.theta);assert_eq!(ch.mu,NCA_CH.mu);assert_eq!(ch.eta,NCA_CH.eta);let a:usize=kani::any();kani::assume(a<10);assert_eq!(ch.zc[a],NCA_CH.zc[a]);
 NCA_STAGE=4;if NCA_MODE==3{return Err(wire::Error::Terminal);}
 let claims=Box::new(NCA_CLAIMS);NCA_CLAIM_PTR=claims.as_ptr().cast::<K>();
 Ok(crate::r1_semantic::Verified{roots:NCA_ROOTS,challenges:ch,alpha:NCA_ALPHA,claims,extra:NCA_EXTRA,before_z1:NCA_BEFORE,state_before_z0:NCA_BEFORE_STATE,z:NCA_Z,transcript:carrier::transcript(carrier::into_hash(t),NCA_STATES[2],27)})
}}
fn NCA_init(bytes:*const u8,p:*const u8,t:*const u8,mode:u8,index:usize){unsafe{
 NCA_STAGE=0;NCA_MODE=mode;NCA_INDEX=index;NCA_BYTES=bytes;NCA_P=p;NCA_T=t;NCA_HASH=kani::any();NCA_STATES=kani::any();NCA_CALLBACKS=0;
 NCA_CH=wire::Challenges{lambda:core::mem::transmute::<[u8;16],K>(kani::any()),chi:core::mem::transmute::<[u8;16],K>(kani::any()),theta:core::mem::transmute::<[u8;16],K>(kani::any()),zc:core::mem::transmute::<[u8;160],[K;10]>(kani::any()),mu:core::mem::transmute::<[u8;16],K>(kani::any()),eta:core::mem::transmute::<[u8;16],K>(kani::any())};
 NCA_ROOTS=kani::any();NCA_ALPHA=core::mem::transmute::<[u8;160],[K;10]>(kani::any());NCA_CLAIMS=core::mem::transmute::<[u8;1392],[[K;29];3]>(kani::any());NCA_EXTRA=core::mem::transmute::<[u8;464],[K;29]>(kani::any());NCA_BEFORE=core::mem::transmute::<[u8;464],[K;29]>(kani::any());NCA_BEFORE_STATE=kani::any();NCA_Z=core::mem::transmute::<[u8;64],[SecureCirclePoint;2]>(kani::any());
}}
'''
# The parser's successful full-length record geometry; no successful parse assumption.
shape=lambda r:32 if r in [2,14] else 896 if 15<=r<=24 else 3712 if r==25 else 928 if r==26 else 0
at=32;records=[]
for r in range(27):
 end=at+5+shape(r);records.append(f'&bytes[{at}..{end}]');at=end
assert at==13831
s=s.replace('RECORDS',','.join(records))
attrs='''#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(crate::r1_wire::Prefix::parse,NCA_Parser::parse)]
#[kani::stub(crate::r1_semantic::public_transcript,NCA_public)]
#[kani::stub(crate::r1_wire::begin,NCA_begin)]
#[kani::stub(crate::r1_semantic::verify_finish,NCA_finish)]
'''
for name,forced,wrong in [('NCA_observed_routes',None,False),('NCA_observed_success',4,False),('NCA_observed_success_wrong',4,True),('NCA_observed_parse_error',0,False),('NCA_observed_public_error',1,False),('NCA_observed_begin_error',2,False)]:
 s+=attrs+'fn '+name+'(){\n'
 s+=' let p:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};let t:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};let bytes:[u8;13831]=kani::any();let index:usize=kani::any();kani::assume(index<32);\n'
 s+=' let mode:u8='+('kani::any()' if forced is None else str(forced))+';kani::assume(mode<5);NCA_init(bytes.as_ptr(),&p as *const _ as *const u8,&t as *const _ as *const u8,mode,index);\n'
 s+=' let result=crate::r1_semantic::verify_observed(Public::Transfer(&p,&t),&bytes,unsafe{NCA_Digest(NCA_HASH)},None);\n unsafe{match result{\n'
 s+=' Err(wire::Error::Length{row})=>{assert_eq!(mode,0);assert_eq!(row,0);assert_eq!(NCA_STAGE,1);kani::cover!(true,"parse failure has no child suffix");},\nErr(wire::Error::Public)=>{assert_eq!(mode,1);assert_eq!(NCA_STAGE,2);kani::cover!(true,"public failure has no begin");},\nErr(wire::Error::RowOrder{expected,actual})=>{assert_eq!(mode,2);assert_eq!(expected,0);assert_eq!(actual,1);assert_eq!(NCA_STAGE,3);kani::cover!(true,"begin failure has no finish");},\nErr(wire::Error::Terminal)=>{assert_eq!(mode,3);assert_eq!(NCA_STAGE,4);kani::cover!(true,"finish error returned unchanged");},\n'
 s+=' Ok(v)=>{assert_eq!(mode,4);assert_eq!(NCA_STAGE,4);let b:usize=kani::any();let a:usize=kani::any();let point:usize=kani::any();let lane:usize=kani::any();kani::assume(b<2&&a<10&&point<3&&lane<29);\n'
 s+=('assert_ne!' if wrong else 'assert_eq!')+'(v.roots[b][index],NCA_ROOTS[b][index]);\n'
 s+='assert_eq!(v.alpha[a],NCA_ALPHA[a]);assert_eq!(v.claims[point][lane],NCA_CLAIMS[point][lane]);assert_eq!(v.claims.as_ptr().cast::<K>(),NCA_CLAIM_PTR);assert_eq!(v.extra[lane],NCA_EXTRA[lane]);assert_eq!(v.before_z1[lane],NCA_BEFORE[lane]);assert_eq!(v.state_before_z0[index],NCA_BEFORE_STATE[index]);assert_eq!(v.z[b],NCA_Z[b]);assert_eq!(v.transcript.state()[index],NCA_STATES[2][index]);assert_eq!(v.transcript.next_row(),27);assert_eq!(v.challenges.lambda,NCA_CH.lambda);assert_eq!(v.challenges.chi,NCA_CH.chi);assert_eq!(v.challenges.theta,NCA_CH.theta);assert_eq!(v.challenges.zc[a],NCA_CH.zc[a]);assert_eq!(v.challenges.mu,NCA_CH.mu);assert_eq!(v.challenges.eta,NCA_CH.eta);kani::cover!(true,"complete returned Verified carrier");},\n _=>assert!(false,"unexpected semantic Result")};assert_eq!(NCA_CALLBACKS,0);}\n}\n'
(E/'NCA_semantic.rs.txt').write_text(s);Path('/private/tmp/NCA_semantic.rs').write_text(s)

# Matching wrong error/stage assertions in exactly the same source configuration.
s=s.replace('fn NCA_observed_parse_error()', 'fn NCA_observed_parse_error()')
for name,before,after in [('parse','assert_eq!(row,0);','assert_ne!(row,0);'),('public','assert_eq!(NCA_STAGE,2);','assert_ne!(NCA_STAGE,2);'),('begin','assert_eq!(actual,1);','assert_ne!(actual,1);')]:
 start=s.index(attrs+'fn NCA_observed_'+name+'_error()')
 end=s.find(attrs,start+len(attrs))
 block=s[start:] if end<0 else s[start:end]
 block=block.replace('fn NCA_observed_'+name+'_error()', 'fn NCA_observed_'+name+'_wrong()').replace(before,after)
 s+='\n'+block
(E/'NCA_semantic.rs.txt').write_text(s);Path('/private/tmp/NCA_semantic.rs').write_text(s)
