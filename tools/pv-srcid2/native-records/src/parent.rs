//! Import the exact shipped module by path, without editing or copying its body.
#![allow(dead_code)]
pub use aspis_statement::pool_v1::*;
#[path = "../../../../crates/aspis-statement/src/pool_v1/pair_trace.rs"]
mod pair_trace;
#[path = "../../../../crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs"]
mod shipped;
use aspis_core::field::M31;
use pair_forest_trace::PoolV1PairForestInputNoteWitnessV1;
use aspis_statement::pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1;
use pair_tree_profile::{PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1};
use payment_relation::{PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1};

pub fn check() {
    let z = [M31::ZERO; 8];
    let input = PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key: z, salt: z, value: 0,
            pair_leaf: PoolV1PairLeafWitnessV1 {
                first_commitment: z, second_occupied: M31::ZERO,
                second_commitment: z, second_occupancy_inverse: M31::ZERO,
            },
            selected_second: false,
            membership: PoolV1MembershipWitnessV1 { siblings: [z; 20], index: 0 },
        },
        super_root_siblings: [z; 3], super_root_directions: [false; 3],
    };
    let change = PoolV1OutputNoteWitnessV1 { owner_key: z, salt: z, value: 0 };
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: [0; 32], deployment_domain: [0; 32], sequence: 0,
        next_pair_index: 0, current_root: z, frontier: [z; 20],
    };
    let r = shipped::CopyRecords::new(&input, 1 << 30, None, &change, &snapshot, M31::ZERO);
    let b = r.banks().expect("the actual mapper and bank constructor return successfully");
    // Actual writer layout: output j=1 has base row 1008+2j, raw column 10.
    // These checks intentionally assert the malformed value is preserved.
    assert_eq!(b.merged[10][1010].0, 1 << 30);
    assert!(b.merged[10][1010].0 >= (1 << 30));
    println!("ACTUAL_SOURCE_BOUNDARY: output raw value = {}, required WitnessOk bound < {}", b.merged[10][1010].0, 1u32 << 30);
    println!("MAPPER_AND_BANKS_SUCCEEDED_WITH_OUTSIDE_WORDS_DOMAIN");
}
