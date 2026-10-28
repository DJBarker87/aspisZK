use super::*;
#[derive(Clone,Copy)] struct NBL_Digest;
static mut NBL_CALLS:usize=0;
static mut NBL_PUBLIC:*const ()=core::ptr::null();
static mut NBL_TRANSITION:*const ()=core::ptr::null();
static mut NBL_WITHDRAW:bool=false;
static mut NBL_SEM:*const u8=core::ptr::null();
static mut NBL_ENTERED:bool=false;
impl Digest32 for NBL_Digest { fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
 assert_eq!(parts.len(),1);assert_eq!(parts[0].as_ptr(),NBL_SEM);NBL_CALLS+=1;kani::any()
}}}
fn NBL_verify_error<H:Digest32>(public:Public<'_>,bytes:&[u8],hash:H,obs:Observer)->Result<crate::r1_semantic::Verified<H>,crate::r1_wire::Error>{unsafe{
 assert!(!NBL_ENTERED);NBL_ENTERED=true;assert_eq!(bytes.as_ptr(),NBL_SEM);assert_eq!(bytes.len(),13831);assert!(obs.is_none());
 match public{Public::Transfer(p,t)=>{assert!(!NBL_WITHDRAW);assert_eq!(p as *const _ as *const (),NBL_PUBLIC);assert_eq!(t as *const _ as *const (),NBL_TRANSITION);},Public::Withdrawal(p,t)=>{assert!(NBL_WITHDRAW);assert_eq!(p as *const _ as *const (),NBL_PUBLIC);assert_eq!(t as *const _ as *const (),NBL_TRANSITION);}}
 let _=hash.digest(&[bytes]);
 let kind:u8=kani::any();kani::assume(kind<11);
 use crate::r1_wire::Error as W;
 Err(match kind{0=>W::Allocation,1=>W::RowOrder{expected:kani::any(),actual:kani::any()},2=>W::InvalidRow,3=>W::Tag{row:kani::any()},4=>W::Length{row:kani::any()},5=>W::NonCanonical{row:kani::any(),value:kani::any()},6=>W::Boundary{round:kani::any()},7=>W::Terminal,8=>W::EqualCirclePoints,9=>W::TrailingBytes,_=>W::Public})
}}
// Exact continuation after the source's wide_view succeeds. The View is an
// explicit local cut, retaining its original semantic carrier and public input.
fn NBL_after_view<H:Digest32>(public:Public<'_>,v:&View<'_>,hash:H,obs:Observer,g:&mut[E;29])->Result<Box<Prepared>,Error>{
 let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;
 mark(obs,Phase::Semantic);
 Prepared::new(&sem,v,hash,g)
}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(crate::r1_semantic::verify_observed,NBL_verify_error)]
fn NBL_after_view_semantic_error(){
 let transfer:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};
 let withdrawal:aspis_statement::pool_v1::PoolV1WithdrawalPublicV1=unsafe{core::mem::zeroed()};
 let transition:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};
 let withdraw:bool=kani::any();let public=if withdraw{Public::Withdrawal(&withdrawal,&transition)}else{Public::Transfer(&transfer,&transition)};
 let semantic:[u8;13831]=kani::any();let v=View{variant:Variant::S2,semantic:&semantic,y1:&[],inactive:E::ZERO,round0:&[],folded_root:None,round1:&[],final_message:&[],query_bytes:&[]};
 let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};let old=g;let i:usize=kani::any();kani::assume(i<29);
 unsafe{NBL_WITHDRAW=withdraw;NBL_PUBLIC=if withdraw{&withdrawal as *const _ as *const ()}else{&transfer as *const _ as *const ()};NBL_TRANSITION=&transition as *const _ as *const ();NBL_SEM=semantic.as_ptr();NBL_ENTERED=false;NBL_CALLS=0;}
 let result=NBL_after_view(public,&v,NBL_Digest,None,&mut g);
 assert!(matches!(result,Err(Error::Semantic)));assert_eq!(g[i],old[i]);unsafe{assert!(NBL_ENTERED);assert_eq!(NBL_CALLS,1);}
 kani::cover!(withdraw,"withdrawal semantic rejection");kani::cover!(!withdraw,"transfer semantic rejection");
}
