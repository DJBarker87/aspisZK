//! Public deterministic test-witness words. No wallet or entropy key is used.
use aspis_core::field::{M31, P};
use aspis_statement::{derive_owner_key, pool_v1::{pool_v1_note_commitment, pool_v1_tree_parent, PoolV1PairLeafWitnessV1}, poseidon2::Digest};
fn digest(seed: u32) -> Digest {core::array::from_fn(|i| M31((seed + 17 * i as u32 + 1)%P))}
fn raw(d: Digest) -> [u32;8] {d.map(|m| m.0)}
fn main() {
 let commitment=pool_v1_note_commitment(&derive_owner_key(&digest(10)),1000,M31(77),&digest(100));
 let pair=PoolV1PairLeafWitnessV1::two_outputs(commitment,digest(900)).unwrap();
 let mut lane=pair.leaf_digest().unwrap();
 for l in 0..20 {let sibling=digest(2000+20*l);lane=if ((0x54321u32>>l)&1)==0 {pool_v1_tree_parent(&lane,&sibling)}else {pool_v1_tree_parent(&sibling,&lane)};}
 let mut global=lane;
 for (s,reverse) in [(digest(3000),true),(digest(3100),false),(digest(3200),true)] {global=if reverse {pool_v1_tree_parent(&s,&global)}else {pool_v1_tree_parent(&global,&s)};}
 println!("input_commitment={:?}",raw(commitment));
 println!("second_occupancy_inverse={}",pair.second_occupancy_inverse.0);
 println!("lane_anchor={:?}",raw(lane));
 println!("global_anchor={:?}",raw(global));
}
