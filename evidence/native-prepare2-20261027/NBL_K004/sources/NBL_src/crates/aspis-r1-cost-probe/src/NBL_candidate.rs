use super::*;
#[derive(Clone,Copy)] struct NBL_Digest;
impl Digest32 for NBL_Digest { fn digest(&self,_:&[&[u8]])->[u8;32] { kani::any() } }
fn NBL_alloc_fail<T:Copy>(n:usize,_v:T)->Result<Vec<T>,aspis_core::r0::Error>{
 assert_eq!(n,compact::LOGICAL_SEMANTIC+compact::LOGICAL_Y1);assert_eq!(core::mem::size_of::<T>(),1);
 Err(aspis_core::r0::Error::Allocation)
}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(aspis_core::r0::heap::filled::<u8>,NBL_alloc_fail)]
fn NBL_prepare_allocation_error(){
 let transfer:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};
 let transition:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};
 let public=Public::Transfer(&transfer,&transition);
 let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};let old=g;
 let i:usize=kani::any();kani::assume(i<29);
 let result=prepare(public,&[],NBL_Digest,None,&mut g);
 assert!(matches!(result,Err(Error::Allocation)));assert_eq!(g[i],old[i]);
 kani::cover!(true,"allocation rejection returns before proof access and scratch writes");
}
static mut NBL_PROOF:*const u8=core::ptr::null();
static mut NBL_LOGICAL:*mut u8=core::ptr::null_mut();
static mut NBL_EVENTS:usize=0;
const NBL_LOGICAL_BYTES:usize=compact::LOGICAL_SEMANTIC+compact::LOGICAL_Y1;
fn NBL_alloc_any<T:Copy>(n:usize,_v:T)->Result<Vec<T>,aspis_core::r0::Error>{
 assert_eq!(n,NBL_LOGICAL_BYTES);assert_eq!(core::mem::size_of::<T>(),1);assert_eq!(core::mem::align_of::<T>(),1);
 let data=Box::new(kani::any::<[u8;NBL_LOGICAL_BYTES]>());
 let ptr=Box::into_raw(data) as *mut T;
 unsafe{NBL_LOGICAL=ptr as *mut u8;Ok(Vec::from_raw_parts(ptr,n,n))}
}
fn NBL_expand_sem_error(c:&[u8],out:&mut[u8])->Result<(),CodecError>{unsafe{
 assert_eq!(NBL_EVENTS,0);NBL_EVENTS=1;
 assert_eq!(c.as_ptr(),NBL_PROOF.add(compact::OFF_SEMANTIC));assert_eq!(c.len(),compact::OFF_Y1-compact::OFF_SEMANTIC);
 assert_eq!(out.as_ptr(),NBL_LOGICAL);assert_eq!(out.len(),compact::LOGICAL_SEMANTIC);
 let i:usize=kani::any();kani::assume(i<out.len());out[i]=kani::any();
 if kani::any(){Err(CodecError::Length)}else{Err(CodecError::NonCanonical)}
}}
#[kani::proof] #[kani::unwind(3)]
#[kani::stub(aspis_core::r0::heap::filled::<u8>,NBL_alloc_any)]
#[kani::stub(crate::compact::expand_semantic,NBL_expand_sem_error)]
fn NBL_prepare_semantic_expansion_error(){
 let transfer:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1=unsafe{core::mem::zeroed()};
 let transition:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1=unsafe{core::mem::zeroed()};
 let proof:[u8;compact::PROOF_BYTES]=kani::any();
 let mut g:[E;29]=unsafe{core::mem::transmute::<[u8;928],[E;29]>(kani::any())};let old=g;
 let i:usize=kani::any();kani::assume(i<29);
 unsafe{NBL_PROOF=proof.as_ptr();NBL_EVENTS=0;}
 let result=prepare(Public::Transfer(&transfer,&transition),&proof,NBL_Digest,None,&mut g);
 assert!(matches!(result,Err(Error::Parse)));assert_eq!(g[i],old[i]);unsafe{assert_eq!(NBL_EVENTS,1);}
 kani::cover!(true,"semantic expansion rejection preserves caller scratch");
}
