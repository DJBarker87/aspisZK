use aspis_statement::pool_v1::*;
use aspis_core::field::M31;
type Digest=[M31;8];
fn validate_master(
    master: &PoolV1PairForestMasterV1,
) -> Result<(), PoolV1PairForestAccountErrorV1> {
    if master.identity.pool == [0u8; 32]
        || master.identity.asset_mint == [0u8; 32]
        || master.identity.token_program == [0u8; 32]
        || master.identity.deployment_domain == [0u8; 32]
    {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    validate_verifier_policy_v1(&master.verifier_policy)
        .map_err(|_| PoolV1PairForestAccountErrorV1::Policy)?;
    if master
        .last_checkpoint_lane_sequences
        .iter()
        .any(|sequence| *sequence > POOL_V1_PAIR_CAPACITY)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    if (!master.has_checkpoint
        && (master.next_checkpoint_sequence != 0
            || master.last_checkpoint_lane_sequences != [0u64; 8]))
        || (master.has_checkpoint && master.next_checkpoint_sequence == 0)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    Ok(())
}

fn digest_is_canonical(digest: &Digest) -> bool {
    let mut i = 0;
    while i < digest.len() {
        if digest[i].0 >= 2147483647 {
            return false;
        }
        i += 1;
    }
    true
}

fn PoolT_loop(master:&PoolV1PairForestMasterV1,lanes:&[PoolV1PairForestLaneStateV1;8])->Result<[u64;8],PoolV1PairForestAccountErrorV1>{
    let mut lane_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for (expected_lane, lane) in lanes.iter().enumerate() {
        if lane.master != master.identity.pool {
            return Err(PoolV1PairForestAccountErrorV1::LaneMasterMismatch);
        }
        if usize::from(lane.lane_id) != expected_lane {
            return Err(PoolV1PairForestAccountErrorV1::LaneOrderMismatch);
        }
        if lane.tree.next_leaf_index > POOL_V1_PAIR_CAPACITY {
            return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
        }
        lane_sequences[expected_lane] = lane.tree.next_leaf_index;
    }
    Ok(lane_sequences)
}
fn PoolT_tail(master:&PoolV1PairForestMasterV1,lane_sequences:[u64;8])->Result<u64,PoolV1PairForestAccountErrorV1>{
    if master.has_checkpoint {
        let mut progressed = false;
        for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
            if lane_sequences[lane] < master.last_checkpoint_lane_sequences[lane] {
                return Err(PoolV1PairForestAccountErrorV1::LaneSequenceDecreased);
            }
            progressed |= lane_sequences[lane] > master.last_checkpoint_lane_sequences[lane];
        }
        if !progressed {
            return Err(PoolV1PairForestAccountErrorV1::DuplicateCheckpoint);
        }
    }
    let next_sequence = master
        .next_checkpoint_sequence
        .checked_add(1)
        .ok_or(PoolV1PairForestAccountErrorV1::CheckpointSequenceOverflow)?;
    Ok(next_sequence)
}
fn PoolT_assembly(master:&PoolV1PairForestMasterV1,lane_sequences:[u64;8],global_root:Digest,checkpoint_bump:u8,next_sequence:u64)->Result<PoolV1PairForestCheckpointPlanV1,PoolV1PairForestAccountErrorV1>{
    let checkpoint = PoolV1PairForestCheckpointV1 {
        bump: checkpoint_bump,
        master: master.identity.pool,
        deployment_domain: master.identity.deployment_domain,
        checkpoint_sequence: master.next_checkpoint_sequence,
        global_root,
        lane_sequences,
    };
    let next_master = PoolV1PairForestMasterV1 {
        has_checkpoint: true,
        next_checkpoint_sequence: next_sequence,
        last_checkpoint_lane_sequences: lane_sequences,
        ..*master
    };
    validate_master(&next_master)?;
    Ok(PoolV1PairForestCheckpointPlanV1 {
        next_master,
        checkpoint,
    })
}
fn PoolT_split(
    master: &PoolV1PairForestMasterV1,
    lanes: &[PoolV1PairForestLaneStateV1; POOL_V1_PAIR_FOREST_LANE_COUNT],
    global_root: Digest,
    checkpoint_bump: u8,
) -> Result<PoolV1PairForestCheckpointPlanV1, PoolV1PairForestAccountErrorV1> {
    validate_master(master)?;
    if master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    if !digest_is_canonical(&global_root) {
        return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);
    }
    let lane_sequences=PoolT_loop(master,lanes)?;
    let next_sequence=PoolT_tail(master,lane_sequences)?;
    PoolT_assembly(master,lane_sequences,global_root,checkpoint_bump,next_sequence)
}
#[cfg(kani)] mod PoolT_checks{use super::*;
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
fn PoolT_error_decomposition(){
 let m=arbitrary_master();let lanes=arbitrary_lanes();let root=core::array::from_fn(|_|M31(kani::any()));let bump=kani::any();
 let original=plan_pool_v1_pair_forest_checkpoint_v1(&m,&lanes,root,bump);
 let split=PoolT_split(&m,&lanes,root,bump);
 assert!(original.err()==split.err());
}
}
