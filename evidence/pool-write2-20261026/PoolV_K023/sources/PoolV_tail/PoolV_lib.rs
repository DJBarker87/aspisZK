//! Exact native chronology tail over its accessed fields. Enclosing source joins separate.
use aspis_statement::pool_v1::*;
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
