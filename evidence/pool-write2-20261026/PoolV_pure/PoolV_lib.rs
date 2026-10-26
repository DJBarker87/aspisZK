//! Native pure-source gates. No shipped-source modifications or stubs.
#[cfg(kani)]
mod PoolV_checks {
    use aspis_statement::pool_v1::*;
    use aspis_core::field::M31;
    fn checkpoint() -> PoolV1PairForestCheckpointV1 {
        PoolV1PairForestCheckpointV1 { bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),
            checkpoint_sequence:kani::any(),global_root:core::array::from_fn(|_|M31(kani::any())),lane_sequences:kani::any() }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolV_encode_exact_bindings() {
        let cp=checkpoint();
        if let Ok(image)=encode_pool_v1_pair_forest_checkpoint_v1(&cp) {
            assert!(image.len()==192);
            assert!(image[0..4]==*b"ASC8");assert!(image[4]==2 && image[5]==8 && image[6]==1);
            assert!(image[7]==cp.bump);
            assert!(image[8..40]==cp.master);assert!(image[40..72]==cp.deployment_domain);
            assert!(image[72..80]==cp.checkpoint_sequence.to_le_bytes());
            assert!(image[176..192]==[0u8;16]);
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolV_encode_decode_roundtrip() {
        let cp=checkpoint();
        if let Ok(image)=encode_pool_v1_pair_forest_checkpoint_v1(&cp) {
            assert!(decode_pool_v1_pair_forest_checkpoint_v1(&image)==Ok(cp));
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolV_decode_encode_canonical() {
        let image:[u8;192]=kani::any();
        if let Ok(cp)=decode_pool_v1_pair_forest_checkpoint_v1(&image) {
            assert!(encode_pool_v1_pair_forest_checkpoint_v1(&cp)==Ok(image));
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolV_encode_selected_sequence() {
        let cp=checkpoint();let lane:usize=kani::any();kani::assume(lane<8);
        if let Ok(image)=encode_pool_v1_pair_forest_checkpoint_v1(&cp) {
            let start=112+8*lane;
            assert!(image[start..start+8]==cp.lane_sequences[lane].to_le_bytes());
        }
    }

    fn arbitrary_master() -> PoolV1PairForestMasterV1 {
        PoolV1PairForestMasterV1 {
            bump:kani::any(),identity:PoolIdentityV1 {pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:M31(kani::any()),deployment_domain:kani::any()},
            verifier_policy:VerifierPolicyV1 {flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()},
            initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()
        }
    }
    fn arbitrary_lanes() -> [PoolV1PairForestLaneStateV1;8] {
        core::array::from_fn(|_|PoolV1PairForestLaneStateV1 {
            bump:kani::any(),master:kani::any(),lane_id:kani::any(),tree:IncrementalMerkleTreeV1 {
                next_leaf_index:kani::any(),root:core::array::from_fn(|_|M31(kani::any())),
                frontier:core::array::from_fn(|_|core::array::from_fn(|_|M31(kani::any())))
            }
        })
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_scalars(){
        let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
        if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump) {
assert!(plan.checkpoint.bump==bump && plan.checkpoint.master==m.identity.pool && plan.checkpoint.deployment_domain==m.identity.deployment_domain);
assert!(plan.checkpoint.checkpoint_sequence==m.next_checkpoint_sequence && plan.checkpoint.global_root==root);
assert!(m.next_checkpoint_sequence<u64::MAX && plan.next_master.next_checkpoint_sequence==m.next_checkpoint_sequence+1 && plan.next_master.has_checkpoint);
        }
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_selected_lane(){
        let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
        if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump) {
let i:usize=kani::any();kani::assume(i<8);
assert!(lanes[i].master==m.identity.pool && lanes[i].lane_id as usize==i);
assert!(plan.checkpoint.lane_sequences[i]==lanes[i].tree.next_leaf_index);
assert!(plan.next_master.last_checkpoint_lane_sequences[i]==lanes[i].tree.next_leaf_index);
assert!(plan.checkpoint.lane_sequences[i]<=POOL_V1_PAIR_CAPACITY);
        }
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_selected_monotone(){
        let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
        if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump) {
let i:usize=kani::any();kani::assume(i<8);
assert!(!m.has_checkpoint || plan.checkpoint.lane_sequences[i]>=m.last_checkpoint_lane_sequences[i]);
        }
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_progress(){
        let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
        if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump) {
assert!(!m.has_checkpoint || (0..8).any(|i|plan.checkpoint.lane_sequences[i]>m.last_checkpoint_lane_sequences[i]));
        }
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_master_frame(){
        let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
        if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump) {
assert!(m.initialized_lane_mask==255 && plan.next_master.initialized_lane_mask==m.initialized_lane_mask);
assert!(plan.next_master.identity==m.identity && plan.next_master.verifier_policy==m.verifier_policy && plan.next_master.bump==m.bump);
        }
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_mask(){
let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
if let Ok(_plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump){assert!(m.initialized_lane_mask==255);}
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_no_overflow(){
let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
if let Ok(_plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump){assert!(m.next_checkpoint_sequence<u64::MAX);}
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_sequence(){
let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump){assert!(plan.checkpoint.checkpoint_sequence==m.next_checkpoint_sequence && plan.next_master.next_checkpoint_sequence==m.next_checkpoint_sequence.wrapping_add(1));}
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_no_duplicate(){
let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
kani::assume(m.has_checkpoint);for i in 0..8{kani::assume(lanes[i].tree.next_leaf_index==m.last_checkpoint_lane_sequences[i]);}assert!(plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump).is_err());
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_sequence_binding(){
let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
let i:usize=kani::any();kani::assume(i<8);if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump){assert!(plan.checkpoint.lane_sequences[i]==lanes[i].tree.next_leaf_index);}
    }
    #[kani::proof]
    #[kani::unwind(80)]
    fn PoolV_plan_capacity(){
let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
let i:usize=kani::any();kani::assume(i<8);if let Ok(plan)=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump){assert!(plan.checkpoint.lane_sequences[i]<=POOL_V1_PAIR_CAPACITY);}
    }
}
