//! Exact native chronology tail over its accessed fields. Enclosing source joins separate.
use aspis_statement::pool_v1::*;
use aspis_core::field::M31;
struct PoolV_Master { has_checkpoint:bool,last_checkpoint_lane_sequences:[u64;8],next_checkpoint_sequence:u64 }
fn PoolV_native(master:&PoolV_Master,lane_sequences:[u64;8])->Result<u64,PoolV1PairForestAccountErrorV1>{
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
#[path="../PoolV_ref/PoolV_lib.rs"] mod PoolV_ref;
#[cfg(kani)]
mod PoolV_checks {
use super::*;
#[kani::proof]
#[kani::unwind(80)]
fn PoolV_chronology_native_p6(){
 let new:[u64;8]=kani::any();let old:[u64;8]=kani::any();let has:bool=kani::any();let sequence:u64=kani::any();
 let master=PoolV_Master{has_checkpoint:has,last_checkpoint_lane_sequences:old,next_checkpoint_sequence:sequence};
 let native=PoolV_native(&master,new);
 let (tag,next)=PoolV_ref::chronology(&new,&old,has,sequence);
 let expected=match tag{0=>Ok(next),1=>Err(PoolV1PairForestAccountErrorV1::LaneSequenceDecreased),2=>Err(PoolV1PairForestAccountErrorV1::DuplicateCheckpoint),3=>Err(PoolV1PairForestAccountErrorV1::CheckpointSequenceOverflow),_=>panic!("bad reference tag")};
 assert!(native==expected);
}
}

struct PoolV_Identity {pool:[u8;32]}
struct PoolV_PrefixMaster {identity:PoolV_Identity}
struct PoolV_Tree {next_leaf_index:u64}
struct PoolV_Lane {master:[u8;32],lane_id:u8,tree:PoolV_Tree}
fn PoolV_prefix(master:&PoolV_PrefixMaster,lanes:&[PoolV_Lane;8])->Result<[u64;8],PoolV1PairForestAccountErrorV1>{
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

fn PoolV_assembly(master:&PoolV1PairForestMasterV1,lane_sequences:[u64;8],global_root:[M31;8],checkpoint_bump:u8,next_sequence:u64)->Result<PoolV1PairForestCheckpointPlanV1,PoolV1PairForestAccountErrorV1>{
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
#[cfg(kani)]
mod PoolV_more {
use super::*;
#[kani::proof]
#[kani::unwind(80)]
fn PoolV_native_prefix(){
 let master=PoolV_PrefixMaster{identity:PoolV_Identity{pool:kani::any()}};
 let lanes=core::array::from_fn(|_|PoolV_Lane{master:kani::any(),lane_id:kani::any(),tree:PoolV_Tree{next_leaf_index:kani::any()}});
 if let Ok(sequences)=PoolV_prefix(&master,&lanes){
  for i in 0..8 {assert!(lanes[i].master==master.identity.pool && lanes[i].lane_id as usize==i && lanes[i].tree.next_leaf_index<=POOL_V1_PAIR_CAPACITY && sequences[i]==lanes[i].tree.next_leaf_index);}
 }
}
    fn arbitrary_master() -> PoolV1PairForestMasterV1 {
        PoolV1PairForestMasterV1 {
            bump:kani::any(),identity:PoolIdentityV1 {pool:kani::any(),asset_mint:kani::any(),token_program:kani::any(),asset_id:M31(kani::any()),deployment_domain:kani::any()},
            verifier_policy:VerifierPolicyV1 {flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()},
            initialized_lane_mask:kani::any(),has_checkpoint:kani::any(),next_checkpoint_sequence:kani::any(),last_checkpoint_lane_sequences:kani::any()
        }
    }
#[kani::proof]
#[kani::unwind(80)]
fn PoolV_native_assembly(){
 let m=arbitrary_master();let sequences:[u64;8]=kani::any();let root=core::array::from_fn(|_|aspis_core::field::M31(kani::any()));let bump:u8=kani::any();let next:u64=kani::any();
 if let Ok(plan)=PoolV_assembly(&m,sequences,root,bump,next){
 assert!(plan.checkpoint.master==m.identity.pool && plan.checkpoint.deployment_domain==m.identity.deployment_domain && plan.checkpoint.bump==bump && plan.checkpoint.global_root==root && plan.checkpoint.checkpoint_sequence==m.next_checkpoint_sequence && plan.checkpoint.lane_sequences==sequences);
 assert!(plan.next_master.has_checkpoint && plan.next_master.next_checkpoint_sequence==next && plan.next_master.last_checkpoint_lane_sequences==sequences);
 assert!(plan.next_master.identity==m.identity && plan.next_master.verifier_policy==m.verifier_policy && plan.next_master.bump==m.bump && plan.next_master.initialized_lane_mask==m.initialized_lane_mask);
 }
}
}
