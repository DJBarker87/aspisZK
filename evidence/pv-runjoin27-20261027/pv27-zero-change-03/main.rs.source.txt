//! Counterexample data are the public deterministic fixture; no wallet key.
use aspis_core::field::{M31, P};
use aspis_statement::pool_v1::pair_trace::{PoolV1PairInputNoteWitnessV1, PoolV1PairTraceErrorV1};
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
 for value in [750,0] {
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
  match (value,result) {
   (750,Ok(_))=>println!("control=Ok"),
   (0,Err(e))=>{assert!(matches!(e,PoolV1PairTraceErrorV1::Conservation));println!("full_withdrawal=Err({:?})",e);},
   (_,other)=>panic!("unexpected result: {:?}",other.map(|_|())),
  }
 }
}
