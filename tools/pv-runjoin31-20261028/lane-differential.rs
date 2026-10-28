//! Finite validation; original body is generated verbatim from frozen source.
use aspis_core::field::{M31,P};
use aspis_statement::{poseidon2::Digest,pool_v1::{*,pair_trace::{PoolV1PairInputNoteWitnessV1,PoolV1PairTraceErrorV1}}};
use pv_runjoin31_lane_reference::lane_root;
fn frozen_lane_root(input: &PoolV1PairInputNoteWitnessV1) -> Result<Digest, PoolV1PairTraceErrorV1> {
    let mut current = input
        .pair_leaf
        .leaf_digest()
        .map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    for level in 0..20 {
        let sibling = input.membership.siblings[level];
        current = if ((input.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &current)
        };
    }
    Ok(current)
}

fn digest(seed: u32) -> Digest {core::array::from_fn(|i| M31((seed + 17*i as u32 + 1)%P))}
fn main() {
 let mut count=0;
 for seed in 0..128u32 {
  for index in [0,1,2,3,0x54321,0xfffff,0x100000,u32::MAX] {
   let mut input=PoolV1PairInputNoteWitnessV1 {nullifier_key:digest(10),salt:digest(100),value:1000,
    pair_leaf:PoolV1PairLeafWitnessV1::two_outputs(digest(100+seed),digest(900+seed)).unwrap(),selected_second:false,
    membership:PoolV1MembershipWitnessV1 {siblings:core::array::from_fn(|l|digest(2000+20*l as u32+seed)),index}};
   for mutation in 0..4 {
    if mutation==1 {input.pair_leaf.second_occupied=M31::ZERO;}
    if mutation==2 {input.pair_leaf.first_commitment[0]=M31(P);}
    if mutation==3 {input.pair_leaf.second_occupancy_inverse=M31::ZERO;}
    let frozen=frozen_lane_root(&input);let owned=lane_root(input);
    assert_eq!(frozen,owned,"seed={seed} index={index} mutation={mutation}");count+=1;
   }
  }
 }
 println!("lane_native_finite_differential={count}; matched complete Result including leaf failures");
}
