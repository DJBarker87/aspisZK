use aspis_statement::pool_v1::*;
use aspis_core::field::M31;
#[cfg(kani)] mod PoolS2_checks {use super::*;
    fn arbitrary_master() -> PoolV1PairForestMasterV1 {
        PoolV1PairForestMasterV1 {
            bump:kani::any(),identity:PoolIdentityV1 {pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:M31(kani::any()),deployment_domain:kani::any()},
            verifier_policy:VerifierPolicyV1 {flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()},
            initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()
        }
    }
fn lanes()->[PoolV1PairForestLaneStateV1;8]{
// Every field in the original lane type is an integer or array of integers.
let raw=kani::any::<[[u8;core::mem::size_of::<PoolV1PairForestLaneStateV1>()];8]>();
unsafe{core::mem::transmute(raw)}
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_bump(){
let m=arbitrary_master();let ls=lanes();let root=kani::any::<[u32;8]>().map(M31);let bump=kani::any();
if let Ok(p)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&ls,root,bump){assert!(p.checkpoint.bump==bump);}
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_bump_first(){
let m=arbitrary_master();let ls=lanes();let root=kani::any::<[u32;8]>().map(M31);let bump=kani::any();
kani::assume(!m.has_checkpoint);
if let Ok(p)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&ls,root,bump){assert!(p.checkpoint.bump==bump);}
}

#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_bump_repeat_bounded(){
let mut m=arbitrary_master();let mut ls=lanes();
m.has_checkpoint=true;m.initialized_lane_mask=255;
for i in 0..8 {let old=kani::any::<u32>() as u64;let new=kani::any::<u32>() as u64;
kani::assume(old<=POOL_V1_PAIR_CAPACITY);kani::assume(new<=POOL_V1_PAIR_CAPACITY);
m.last_checkpoint_lane_sequences[i]=old;ls[i].tree.next_leaf_index=new;}
let root=kani::any::<[u32;8]>().map(M31);let bump=kani::any();
if let Ok(p)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&ls,root,bump){assert!(p.checkpoint.bump==bump);}
}

#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_bump_progress0(){
let mut m=arbitrary_master();let mut ls=lanes();
m.has_checkpoint=true;m.initialized_lane_mask=255;
for i in 0..8 {let old=kani::any::<u32>() as u64;let new=kani::any::<u32>() as u64;
kani::assume(old<=POOL_V1_PAIR_CAPACITY);kani::assume(new<=POOL_V1_PAIR_CAPACITY);
m.last_checkpoint_lane_sequences[i]=old;ls[i].tree.next_leaf_index=new;}
let root=kani::any::<[u32;8]>().map(M31);let bump=kani::any();
if let Ok(p)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&ls,root,bump){assert!(p.checkpoint.bump==bump);}
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_domain(){
 let image:[u8;384]=kani::any();
 if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.identity.deployment_domain==image[176..208]);}
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_token(){
 let image:[u8;384]=kani::any();
 if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.identity.token_program==image[136..168]);}
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_asset(){let image:[u8;384]=kani::any();if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.identity.asset_id.0.to_le_bytes()==image[168..172]);}}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_policy_flags(){let image:[u8;384]=kani::any();if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.verifier_policy.flags==image[213]);}}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_registry(){let image:[u8;384]=kani::any();if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.verifier_policy.registry_program==image[216..248]);}}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_authority(){let image:[u8;384]=kani::any();if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.verifier_policy.registry_authority==image[248..280]);}}

#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_master_policy_binding(){let image:[u8;384]=kani::any();if let Ok(m)=decode_pool_v1_pair_forest_master_v1(&image){assert!(m.verifier_policy.policy_binding==image[280..312]);}}

}
