use aspis_core::field::{M31,P};
use aspis_statement::{derive_owner_key,poseidon2::Digest,pool_v1::{*,pair_trace::PoolV1PairInputNoteWitnessV1,pair_forest_trace::*}};
include!("guard_cut.rs");
#[path="frozen_empty_roots.rs"] mod frozen;
use frozen::POOL_V1_PAIR_EMPTY_ROOTS;
fn digest(seed:u32)->Digest {core::array::from_fn(|i|M31((seed+17*i as u32+1)%P))}
fn canonical(d:&Digest){assert!(d.iter().all(|x|x.0<P))}
fn main(){
 assert!(!cfg!(debug_assertions));
 if std::env::args().nth(1).as_deref()==Some("inverse-only"){inverse_cases();return}
 let key=digest(10);let salt=digest(100);let asset=M31(77);
 let cm=pool_v1_note_commitment(&derive_owner_key(&key),1000,asset,&salt);
 let input=PoolV1PairForestInputNoteWitnessV1 {
  pair:PoolV1PairInputNoteWitnessV1 {nullifier_key:key,salt,value:1000,
   pair_leaf:PoolV1PairLeafWitnessV1::single_output(cm).unwrap(),selected_second:false,
   membership:PoolV1MembershipWitnessV1 {siblings:core::array::from_fn(|l|digest(2000+20*l as u32)),index:0x54321}},
  super_root_siblings:[digest(3000),digest(3100),digest(3200)],super_root_directions:[true,false,true]};
 let mut anchor=input.pair.pair_leaf.leaf_digest().unwrap();
 for l in 0..20 {let sib=input.pair.membership.siblings[l];anchor=if input.pair.membership.index>>l&1==0 {pool_v1_tree_parent(&anchor,&sib)}else{pool_v1_tree_parent(&sib,&anchor)}}
 for l in 0..3 {let sib=input.super_root_siblings[l];anchor=if input.super_root_directions[l] {pool_v1_tree_parent(&sib,&anchor)}else{pool_v1_tree_parent(&anchor,&sib)}}
 let empty=&POOL_V1_PAIR_EMPTY_ROOTS;
 let tree=IncrementalMerkleTreeV1::from_parts_with_empty_roots(0,empty[20],core::array::from_fn(|l|empty[l]),empty).unwrap();
 let lane=PoolV1PairForestLaneStateV1{bump:0,master:[1;32],lane_id:0,tree};
 let lane_bytes=encode_pool_v1_pair_forest_lane_state_v1(&lane,empty).unwrap();
 let lane=decode_pool_v1_pair_forest_lane_state_v1(&lane_bytes,empty).unwrap();
 let cp=PoolV1PairForestCheckpointV1{bump:0,master:[1;32],deployment_domain:[5;32],checkpoint_sequence:42,global_root:anchor,lane_sequences:[0;8]};
 let cp=decode_pool_v1_pair_forest_checkpoint_v1(&encode_pool_v1_pair_forest_checkpoint_v1(&cp).unwrap()).unwrap();
 let snapshot=PoolV1PairLiveSnapshotV1{pool:[1;32],deployment_domain:[5;32],sequence:lane.tree.next_leaf_index,next_pair_index:lane.tree.next_leaf_index,current_root:lane.tree.root,frontier:lane.tree.frontier};
 let context=PoolV1PaymentRelationContextV1{runtime_binding:PoolV1PaymentRuntimeBindingV1{pool:[1;32],deployment_domain:[5;32],anchor_sequence:42,anchor_root:cp.global_root,asset_id:asset},spent_nullifiers:&[]};
 for withdrawal in [false,true] {
  let recipient=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&digest(300)),salt:digest(400),value:600};
  let change=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&digest(500)),salt:digest(600),value:if withdrawal{750}else{400}};
  for d in [&recipient.owner_key,&recipient.salt,&change.owner_key,&change.salt]{canonical(d)}
  let transfer=PoolV1PrivateTransferPublicV1{pool:[1;32],deployment_domain:[5;32],anchor_sequence:42,anchor_root:anchor,nullifier:pool_v1_nullifier(&key,&salt),asset_id:asset,recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,recipient.value,asset,&recipient.salt),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,asset,&change.salt)};
  let wd=PoolV1WithdrawalPublicV1{pool:[1;32],deployment_domain:[5;32],anchor_sequence:42,anchor_root:anchor,nullifier:transfer.nullifier,asset_id:asset,amount:250,destination_token_account:[9;32],change_commitment:transfer.change_commitment};
  let compiled=if withdrawal{compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&wd,&PoolV1PairForestWithdrawalWitnessV1{input,change},context,snapshot)}else{compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&transfer,&PoolV1PairForestPrivateTransferWitnessV1{input,recipient,change},context,snapshot)}.unwrap();
  for col in &compiled.semantic_c1.c1{check_base_column(col).unwrap()}
  let masks=pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
  let hiding=aspis_core::state_only_hiding::StateOnlyHidingContext::pool_v1_pair_forest_v1([13;32],[17;32]);
  let mut store=aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
  let material=aspis_prover::state_only_hiding::build_pool_v1_pair_forest_mask_material_v1(aspis_prover::HOST_HASH,[23;32],hiding,[19;32],&mut store).unwrap();
  let mut noised=compiled.semantic_c1.clone();
  let applied=aspis_prover::state_only_hiding::apply_pool_v1_pair_forest_mask_material_v1(&mut noised,material).unwrap();
  for col in noised.c1.iter().chain(applied.mask_only_c1.iter()){check_base_column(col).unwrap();assert_eq!(inactive_sum_m31(col,&masks),M31::ZERO)}
  let public=if withdrawal{pair_forest_semantic_terminal::r0::Public::Withdrawal(&wd,&compiled.public_statement)}else{pair_forest_semantic_terminal::r0::Public::Transfer(&transfer,&compiled.public_statement)};
  let full=aspis_r1_cost_probe::prover::prove_masked_fixture(public,&compiled,aspis_r1_cost_probe::transport::Variant::S2,aspis_prover::HOST_HASH,&[29;32]);
  println!("withdrawal={withdrawal} account_decode=Ok full_compiler=Ok raw_C1_canonical=16 masked_base_canonical=26 native_inactive_balanced=26 full_prover={:?}",full.as_ref().map(|_|()));
  assert!(full.is_ok(),"canonical route diagnostic must pass the actual prover");
 }
 println!("finite_native_canonical_route_cases=2; source-generated-output_fields=true; account_codec=true; no_selected_planner_reconstruction_claim=true");
}

fn mod_pow(mut base:u64,mut exponent:u32)->u32{let mut acc=1u64;while exponent!=0{if exponent&1!=0{acc=acc*base%u64::from(P)}base=base*base%u64::from(P);exponent>>=1;}acc as u32}
fn inverse_cases(){
 let mut cases=vec![1,2,P-1];for i in 0..128u64{cases.push(((i*1664525+1013904223)%u64::from(P-1)+1) as u32)}
 for x in &cases{let got=M31(*x).inv();assert_eq!(got.0,mod_pow(u64::from(*x),P-2));assert!(got.0<P);assert_eq!(M31(*x).mul(got),M31::ONE)}
 let raw=[0,1,P-1,P,u32::MAX];let mut products=0;for x in raw{for y in raw{assert_eq!(M31(x).mul(M31(y)).0,(u64::from(x)*u64::from(y)%u64::from(P)) as u32);products+=1}}
 let zero=std::panic::catch_unwind(||M31::ZERO.inv());assert!(zero.is_err());
 println!("same_input_native_inverse_modpow_comparisons={} widened_product_comparisons={products} zero_inverse_expected_panic=true finite_validation_only=true",cases.len());
}
