//! Counterexample data are the public deterministic fixture; no wallet key.
use aspis_core::field::{M31, P};
use aspis_statement::pool_v1::pair_trace::{PoolV1PairInputNoteWitnessV1};
use aspis_statement::{derive_owner_key, pool_v1::*, poseidon2::Digest};
fn digest(seed: u32) -> Digest {core::array::from_fn(|i| M31((seed + 17*i as u32 + 1)%P))}
fn main() {
 let sk=digest(10);let salt=digest(100);let asset=M31(77);
 let leaf=pool_v1_note_commitment(&derive_owner_key(&sk),1000,asset,&salt);
 let input=PoolV1PairForestInputNoteWitnessV1 {
  pair: PoolV1PairInputNoteWitnessV1 {nullifier_key:sk,salt,value:1000,
   pair_leaf:PoolV1PairLeafWitnessV1::two_outputs(leaf,digest(900)).unwrap(),selected_second:false,
   membership:PoolV1MembershipWitnessV1 {siblings:core::array::from_fn(|l|digest(2000+20*l as u32)),index:0x54321}},
  super_root_siblings:[digest(3000),digest(3100),digest(3200)],super_root_directions:[true,false,true]};
 let mut anchor=input.pair.pair_leaf.leaf_digest().unwrap();
 for l in 0..20 {let s=input.pair.membership.siblings[l];anchor=if (input.pair.membership.index>>l)&1==0 {pool_v1_tree_parent(&anchor,&s)}else{pool_v1_tree_parent(&s,&anchor)};}
 for l in 0..3 {anchor=if input.super_root_directions[l] {pool_v1_tree_parent(&input.super_root_siblings[l],&anchor)}else{pool_v1_tree_parent(&anchor,&input.super_root_siblings[l])};}
 let mut empty=[[M31::ZERO;8];21];empty[0]=pool_v1_tree_parent(&[M31::ZERO;8],&[M31::ZERO;8]);
 for l in 0..20 {empty[l+1]=pool_v1_tree_parent(&empty[l],&empty[l]);}
 let snapshot=PoolV1PairLiveSnapshotV1 {pool:[1;32],deployment_domain:[5;32],sequence:0,next_pair_index:0,current_root:empty[20],frontier:core::array::from_fn(|l|empty[l])};
 for value in [750] {
  let change=PoolV1OutputNoteWitnessV1 {owner_key:digest(700),salt:digest(800),value};
  let public=PoolV1WithdrawalPublicV1 {pool:[1;32],deployment_domain:[5;32],anchor_sequence:0,anchor_root:anchor,
   nullifier:pool_v1_nullifier(&sk,&salt),asset_id:asset,amount:1000-value,destination_token_account:[6;32],
   change_commitment:pool_v1_note_commitment(&change.owner_key,value,asset,&change.salt)};
  let context=PoolV1PaymentRelationContextV1 {runtime_binding:PoolV1PaymentRuntimeBindingV1 {pool:public.pool,deployment_domain:public.deployment_domain,anchor_sequence:0,anchor_root:anchor,asset_id:asset},spent_nullifiers:&[]};
  validate_pool_v1_withdrawal_public_v1(&public).unwrap();
  assert_eq!(public.amount+change.value,input.pair.value);
  let witness=PoolV1PairForestWithdrawalWitnessV1 {input,change};
  let result=compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public,&witness,context,snapshot);
  println!("amount={} change={} change_commitment={:?}",public.amount,value,public.change_commitment.map(|x|x.0));
  assert!(result.is_ok(), "canonical control failed: {:?}", result.as_ref().err());
  println!("canonical_control=Ok");
  let mut altered=snapshot;
  altered.sequence=1; altered.next_pair_index=1;
  altered.frontier[0]=[M31(P);8];
  let mut root=empty[0];
  for level in 0..20 {
   root=if (altered.next_pair_index>>level)&1==0 {
    pool_v1_tree_parent(&root,&empty[level])
   } else { pool_v1_tree_parent(&altered.frontier[level],&root) };
  }
  altered.current_root=root;
  let tree=IncrementalMerkleTreeV1::from_parts_with_empty_roots(
   altered.next_pair_index,altered.current_root,altered.frontier,&empty);
  assert!(tree.is_ok(), "tree validator rejected: {:?}",tree.as_ref().err());
  println!("tree_validation=Ok frontier00={} index={}", altered.frontier[0][0].0,altered.next_pair_index);
  let prepared=compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public,&witness,context,altered);
  match prepared {
   Ok(compiled)=> {
    assert_eq!(compiled.public_statement.live_snapshot,altered);
    assert_eq!(compiled.public_statement.live_snapshot.frontier[0][0].0,P);
    assert_eq!(compiled.trace.afterstate,compiled.public_statement.candidate_afterstate);
    println!("noncanonical_frontier_preparation=Ok retained_frontier00={}",compiled.public_statement.live_snapshot.frontier[0][0].0);
    let mut bytes=[0u8;POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
    let encoded=encode_pool_v1_pair_live_snapshot_v1(&altered,&mut bytes);
    println!("snapshot_codec={:?}",encoded);
    assert!(matches!(encoded,Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest)));
   },
   Err(e)=> panic!("candidate preparation rejected: {:?}",e),
  }
 }
}
