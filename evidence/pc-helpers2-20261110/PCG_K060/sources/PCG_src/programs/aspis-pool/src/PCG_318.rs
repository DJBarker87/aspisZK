use super::*;
use crate::PCG_Address::{Context,reference,KMX_copy_nonoverlapping};
fn parent_reply(seeds:&[&[u8]],program:&Pubkey,key:&Pubkey)->bool{
 let c=unsafe{&*(program as *const Pubkey as *const Context<'_>)};
 assert_eq!(seeds.len(),c.request.count);
 for i in 0..c.request.count{assert_eq!(seeds[i],&c.request.seeds[i][..c.request.lengths[i]]);}
 assert_eq!(*key,c.reply);c.calls.set(c.calls.get()+1);c.is_ok
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(crate::registry::stored_bump_address_matches,parent_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn master_request(){
 let mint:[u8;32]=kani::any();let bump:u8=kani::any();let program:[u8;32]=kani::any();
 let master=PoolV1PairForestMasterV1{bump,identity:aspis_statement::pool_v1::PoolIdentityV1{pool:[0;32],asset_mint:mint,token_program:[0;32],asset_id:aspis_core::field::M31::ZERO,deployment_domain:[0;32]},verifier_policy:aspis_statement::pool_v1::VerifierPolicyV1{flags:0,registry_program:[0;32],registry_authority:[0;32],policy_binding:[0;32]},initialized_lane_mask:0,has_checkpoint:false,next_checkpoint_sequence:0,last_checkpoint_lane_sequences:[0;8]};
 let mut domain=[0u8;32];for i in 0..POOL_V1_PAIR_FOREST_MASTER_SEED.len(){domain[i]=POOL_V1_PAIR_FOREST_MASTER_SEED[i];}let mut bump_seed=[0u8;32];bump_seed[0]=bump;
 let c=Context{program:Pubkey::new_from_array(program),request:reference::Request{program,seeds:[domain,mint,bump_seed,[0;32]],lengths:[POOL_V1_PAIR_FOREST_MASTER_SEED.len(),32,1,0],count:3},outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:0,is_ok:kani::any(),error:0,calls:core::cell::Cell::new(0)};
 let got=master_address_matches(&c.program,&master,&c.reply);assert_eq!(c.calls.get(),1);assert!((got==c.is_ok)!=cfg!(PCG_NEG_MASTER));
}
