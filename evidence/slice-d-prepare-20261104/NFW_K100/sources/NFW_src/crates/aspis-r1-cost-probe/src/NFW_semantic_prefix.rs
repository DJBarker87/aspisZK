use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use crate::NFW_public::{Inputs,Hash};
fn error(bytes:&[u8])->Error{match bytes[0]%11{0=>Error::Allocation,1=>Error::RowOrder{expected:bytes[1],actual:bytes[2]},2=>Error::InvalidRow,3=>Error::Tag{row:bytes[1]},4=>Error::Length{row:bytes[1]},5=>Error::NonCanonical{row:bytes[1],value:usize::from_le_bytes([bytes[3],bytes[4],bytes[5],bytes[6],bytes[7],bytes[8],bytes[9],bytes[10]])},6=>Error::Boundary{round:usize::from_le_bytes([bytes[3],bytes[4],bytes[5],bytes[6],bytes[7],bytes[8],bytes[9],bytes[10]])},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
fn prefix(bytes:&[u8])->Result<Prefix<'_>,Error>{Err(error(bytes))}
fn verify_error(){let p=Inputs::new();let b:[u8;32]=kani::any();let out=verify_observed(p.public(kani::any()),&b,Hash,None);assert!(matches!(out,Err(e) if e==error(&b))!=cfg!(NFW_invert));}
struct SemanticOps{fail:u8,error:Error,calls:usize,bytes:usize,public:(usize,usize,bool),prefix_address:usize,transcript_address:usize,before:[u8;32],after:[u8;32],next_before:u8,next_after:u8,challenges:Challenges,result:Option<Verified<Hash>>,probe:usize}
fn semantic_public(p:Public<'_>)->(usize,usize,bool){match p{Public::Transfer(a,b)=>(a as *const _ as usize,b as *const _ as usize,false),Public::Withdrawal(a,b)=>(a as *const _ as usize,b as *const _ as usize,true)}}
fn semantic_q()->QM31{use aspis_core::field::{CM31,M31};QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn semantic_qs<const N:usize>()->[QM31;N]{let mut out=[QM31::ZERO;N];let mut i=0;while i<N{out[i]=semantic_q();i+=1;}out}
fn semantic_challenges()->Challenges{Challenges{lambda:semantic_q(),chi:semantic_q(),theta:semantic_q(),zc:semantic_qs(),mu:semantic_q(),eta:semantic_q()}}
fn semantic_verified()->Verified<Hash>{Verified{roots:kani::any(),challenges:semantic_challenges(),alpha:semantic_qs(),claims:Box::new([semantic_qs(),semantic_qs(),semantic_qs()]),extra:semantic_qs(),before_z1:semantic_qs(),state_before_z0:kani::any(),z:[SecureCirclePoint{x:semantic_q(),y:semantic_q()},SecureCirclePoint{x:semantic_q(),y:semantic_q()}],transcript:crate::r1_wire::NFW_wire::seed(Hash,kani::any(),kani::any())}}
fn semantic_coordinate(c:&Challenges,i:usize)->QM31{match i{0=>c.lambda,1=>c.chi,2=>c.theta,3..=12=>c.zc[i-3],13=>c.mu,_=>c.eta}}
impl SemanticOps{
 fn parse<'a>(&mut self,bytes:&'a[u8])->Result<Prefix<'a>,Error>{self.calls+=1;assert!(self.calls==1&&bytes.as_ptr() as usize==self.bytes&&bytes.len()==13831);if self.fail==0{return Err(self.error);}let root:&[u8;32]=(&bytes[..32]).try_into().unwrap();Ok(crate::r1_wire::NFW_prefix_wire::prefix(root,[&bytes[32..32];27]))}
 fn public_transcript(&mut self,public:Public<'_>,hash:Hash,root:&[u8;32])->Result<SemanticTranscript<Hash>,Error>{self.calls+=1;assert!(self.calls==2&&semantic_public(public)==self.public&&root.as_ptr() as usize==self.bytes);if self.fail==1{return Err(self.error);}Ok(crate::r1_wire::NFW_wire::seed(hash,self.before,self.next_before))}
 fn begin(&mut self,prefix:&Prefix<'_>,transcript:&mut SemanticTranscript<Hash>)->Result<Challenges,Error>{self.calls+=1;assert!(self.calls==3&&prefix as *const _ as usize==self.prefix_address&&prefix.c1_root.as_ptr() as usize==self.bytes&&transcript as *const _ as usize==self.transcript_address&&transcript.state()==self.before&&crate::r1_wire::NFW_prefix_wire::cursor(transcript)==self.next_before);*transcript=crate::r1_wire::NFW_wire::seed(Hash,self.after,self.next_after);if self.fail==2{Err(self.error)}else{Ok(Challenges{lambda:self.challenges.lambda,chi:self.challenges.chi,theta:self.challenges.theta,zc:self.challenges.zc,mu:self.challenges.mu,eta:self.challenges.eta})}}
 fn finish(&mut self,public:Public<'_>,prefix:Prefix<'_>,transcript:SemanticTranscript<Hash>,challenges:Challenges,_:crate::verifier::Observer)->Result<Verified<Hash>,Error>{self.calls+=1;assert!(self.calls==4&&semantic_public(public)==self.public&&prefix.c1_root.as_ptr() as usize==self.bytes&&transcript.state()==self.after&&crate::r1_wire::NFW_prefix_wire::cursor(&transcript)==self.next_after&&semantic_coordinate(&challenges,self.probe)==semantic_coordinate(&self.challenges,self.probe));if self.fail==3{Err(self.error)}else{Ok(self.result.take().unwrap())}}
}
fn semantic_body(public:Public<'_>,bytes:&[u8],hash:Hash,obs:crate::verifier::Observer,ops:&mut SemanticOps)->Result<Verified<Hash>,Error>{

    let prefix = ops.parse(bytes)?;
    ops.prefix_address=&prefix as *const _ as usize;
    mark(obs, 0);
    let mut transcript = ops.public_transcript(public, hash, prefix.c1_root)?;
    ops.transcript_address=&transcript as *const _ as usize;
    let challenges = ops.begin(&prefix, &mut transcript)?;
    mark(obs, 1);
    ops.finish(public, prefix, transcript, challenges, obs)

}
fn semantic_check(){let inputs=Inputs::new();let public=inputs.public(kani::any());let bytes:[u8;13831]=kani::any();let ebytes:[u8;32]=kani::any();let out=semantic_verified();let claim_address=out.claims.as_ref() as *const _ as usize;let roots=out.roots;let fail:u8=kani::any();kani::assume(fail<=4);let probe:usize=kani::any();kani::assume(probe<15);let mut ops=SemanticOps{fail,error:error(&ebytes),calls:0,bytes:bytes.as_ptr() as usize,public:semantic_public(public),prefix_address:0,transcript_address:0,before:kani::any(),after:kani::any(),next_before:kani::any(),next_after:kani::any(),challenges:semantic_challenges(),result:Some(out),probe};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<2&&j<32);let out=semantic_body(public,&bytes,Hash,None,&mut ops);let good=match out{Err(e)=>fail<4&&e==ops.error,Ok(result)=>fail==4&&result.claims.as_ref() as *const _ as usize==claim_address&&result.roots[i][j]==roots[i][j]};assert!((good&&ops.calls==(if fail<4{fail as usize+1}else{4}))!=cfg!(NFW_invert));}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn verify_error_root(){semantic_check();}
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::proof] #[kani::unwind(258)]
fn verify_error_root_renamed(){semantic_check();}
