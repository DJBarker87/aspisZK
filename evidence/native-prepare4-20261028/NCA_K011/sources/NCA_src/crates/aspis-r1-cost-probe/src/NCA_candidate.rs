use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]struct NCA_Digest;
impl Digest32 for NCA_Digest{fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"no digest before prepare cut");[0;32]}}
static mut NCA_PROOF:*const u8=core::ptr::null();static mut NCA_P:*const u8=core::ptr::null();static mut NCA_T:*const u8=core::ptr::null();
static mut NCA_STAGE:u8=0;static mut NCA_SHAPE:bool=false;static mut NCA_SCAN:bool=false;static mut NCA_OBS:bool=false;
fn NCA_shape(proof:&[u8])->Result<Variant,Error>{unsafe{assert_eq!(NCA_STAGE,0);assert_eq!(proof.as_ptr(),NCA_PROOF);assert_eq!(proof.len(),57607);NCA_STAGE=1;if NCA_SHAPE{Ok(Variant::S2)}else{Err(Error::Parse)}}}
fn NCA_scan(proof:&[u8])->Result<(),Error>{unsafe{assert_eq!(NCA_STAGE,1);assert!(NCA_SHAPE);assert_eq!(proof.as_ptr(),NCA_PROOF);assert_eq!(proof.len(),57607);NCA_STAGE=2;if NCA_SCAN{Ok(())}else{Err(Error::Parse)}}}
fn NCA_observe(phase:Phase){unsafe{assert!(NCA_OBS&&NCA_SCAN&&NCA_SHAPE);assert_eq!(phase,Phase::Parsed);assert_eq!(NCA_STAGE,2);NCA_STAGE=3;}}
fn NCA_prepare_cut<H:Digest32>(public:Public<'_>,proof:&[u8],_:H,obs:Observer,g:&mut[E;29])->Result<Box<Prepared>,Error>{unsafe{
 assert!(NCA_SHAPE&&NCA_SCAN);assert_eq!(NCA_STAGE,if NCA_OBS{3}else{2});assert_eq!(obs.is_some(),NCA_OBS);assert_eq!(proof.as_ptr(),NCA_PROOF);assert_eq!(proof.len(),57607);
 match public{Public::Transfer(p,t)=>{assert_eq!(p as *const _ as *const u8,NCA_P);assert_eq!(t as *const _ as *const u8,NCA_T);},_=>assert!(false,"same public variant")}
 let j:usize=kani::any();kani::assume(j<29);assert_eq!(g[j],E::ZERO);
 kani::cover!(NCA_OBS,"source Parsed callback before prepare");kani::cover!(!NCA_OBS,"source None before prepare");kani::assume(false);Err(Error::Parse)
}}
fn NCA_mark(obs:Observer,p:Phase){if let Some(f)=obs{f(p);}}
fn NCA_prefix<H:Digest32>(public:Public<'_>,proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Box<Prepared>,Error>{
 if k!=SPLIT{return Err(Error::Parse);}parse_shape(proof)?;canonical_scan(proof)?;
 if let Some(f)=obs{f(Phase::Parsed);}
 let mut g=[E::ZERO;29];NCA_prepare_cut(public,proof,hash,obs,&mut g)
}
#[kani::proof]#[kani::unwind(3)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(crate::verifier::mark,NCA_mark)]
#[kani::stub(crate::verifier::candidate::parse_shape,NCA_shape)]
#[kani::stub(crate::verifier::candidate::canonical_scan,NCA_scan)]

fn NCA_tx1_scan_fission(){
 let p:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};let t:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};
 let proof:[u8;57607]=kani::any();let k:usize=kani::any();let obs:bool=kani::any();
 unsafe{NCA_PROOF=proof.as_ptr();NCA_P=&p as *const _ as *const u8;NCA_T=&t as *const _ as *const u8;NCA_STAGE=0;NCA_SHAPE=kani::any();NCA_SCAN=kani::any();NCA_OBS=obs;}
 let r=NCA_prefix(Public::Transfer(&p,&t),&proof,k,NCA_Digest,if obs{Some(NCA_observe)}else{None});
 match r{Err(Error::Parse)=>(),_=>assert!(false,"only prefix Parse can return before cut")};
 unsafe{if k!=SPLIT{assert_eq!(NCA_STAGE,0);}else if !NCA_SHAPE{assert_eq!(NCA_STAGE,1);}else{assert!(!NCA_SCAN);assert_eq!(NCA_STAGE,2);}}
}
