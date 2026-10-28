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
