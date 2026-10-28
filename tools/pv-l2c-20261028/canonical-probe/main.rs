use aspis_core::field::{M31,QM31,P},digest::LegacyHashFn;
use aspis_statement::{derive_owner_key,poseidon2::Digest,pool_v1::{*,pair_trace::PoolV1PairInputNoteWitnessV1,pair_forest_trace::*}};
fn digest(seed:u32)->Digest {core::array::from_fn(|i|M31(seed+17*i as u32+1))}
include!("guard_cut.rs");
// A diagnostic backend stops at the first commitment. The guard is in the
// unmodified native library; this backend records whether that guard returned.
#[derive(Default)] struct GuardBoundary { c1_calls: usize }
impl aspis_r1_cost_probe::host_semantic::Commitments for GuardBoundary {
 fn c1(&mut self,_:&[Vec<M31>;26],_:&[QM31;1024])->Result<[u8;32],aspis_r1_cost_probe::host_wire::Error> {
  self.c1_calls+=1; Err(aspis_r1_cost_probe::host_wire::Error::Public)
 }
 fn c2(&mut self,_:&[QM31],_:&[QM31;1024])->Result<[u8;32],aspis_r1_cost_probe::host_wire::Error> {
  panic!("diagnostic stops before C2")
 }
}
fn main() {
 let mut public_before=None;
 let key=digest(10);let salt=digest(100);let asset=M31(77);
 let input=PoolV1PairForestInputNoteWitnessV1 {
  pair:PoolV1PairInputNoteWitnessV1 {nullifier_key:key,salt,value:1000,
   pair_leaf:PoolV1PairLeafWitnessV1::two_outputs(pool_v1_note_commitment(&derive_owner_key(&key),1000,asset,&salt),digest(900)).unwrap(),
   selected_second:false,membership:PoolV1MembershipWitnessV1 {siblings:core::array::from_fn(|l|digest(2000+20*l as u32)),index:0x54321}},
  super_root_siblings:[digest(3000),digest(3100),digest(3200)],super_root_directions:[true,false,true]};
 let mut anchor=input.pair.pair_leaf.leaf_digest().unwrap();
 for l in 0..20 {let sib=input.pair.membership.siblings[l];anchor=if input.pair.membership.index>>l&1==0 {pool_v1_tree_parent(&anchor,&sib)}else{pool_v1_tree_parent(&sib,&anchor)};}
 for l in 0..3 {let sib=input.super_root_siblings[l];anchor=if input.super_root_directions[l] {pool_v1_tree_parent(&sib,&anchor)}else{pool_v1_tree_parent(&anchor,&sib)};}
 let mut empty=[[M31::ZERO;8];21];empty[0]=pool_v1_tree_parent(&[M31::ZERO;8],&[M31::ZERO;8]);for l in 0..20 {empty[l+1]=pool_v1_tree_parent(&empty[l],&empty[l]);}
 let snapshot=PoolV1PairLiveSnapshotV1 {pool:[1;32],deployment_domain:[5;32],sequence:0,next_pair_index:0,current_root:empty[20],frontier:core::array::from_fn(|i|empty[i])};
 let mut bytes=[0u8;800];encode_pool_v1_pair_live_snapshot_v1(&snapshot,&mut bytes).unwrap();
 let decoded=decode_pool_v1_pair_live_snapshot_v1(&bytes).unwrap();assert_eq!(snapshot,decoded);
 for bad in [false,true] {
  let mut recipient=PoolV1OutputNoteWitnessV1 {owner_key:digest(300),salt:digest(400),value:600};
  recipient.owner_key[0]=M31(if bad {P}else{0});
  let change=PoolV1OutputNoteWitnessV1 {owner_key:digest(500),salt:digest(600),value:400};
  let public=PoolV1PrivateTransferPublicV1 {pool:[1;32],deployment_domain:[5;32],anchor_sequence:42,anchor_root:anchor,nullifier:pool_v1_nullifier(&key,&salt),asset_id:asset,recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,recipient.value,asset,&recipient.salt),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,asset,&change.salt)};
  if let Some(previous)=public_before {assert_eq!(public,previous,"same semantic public for the two representations");}else{public_before=Some(public);}
  let witness=PoolV1PairForestPrivateTransferWitnessV1 {input,recipient,change};
  let context=PoolV1PaymentRelationContextV1 {runtime_binding:PoolV1PaymentRuntimeBindingV1 {pool:public.pool,deployment_domain:public.deployment_domain,anchor_sequence:public.anchor_sequence,anchor_root:public.anchor_root,asset_id:public.asset_id},spent_nullifiers:&[]};
  let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,context,decoded).expect("canonical snapshot decode then full compiler success");
  let bad_cells:Vec<_>=compiled.semantic_c1.c1.iter().enumerate().flat_map(|(c,col)|col.iter().enumerate().filter_map(move |(r,x)|if x.0>=P {Some((c,r,x.0))}else{None})).collect();
  println!("case_noncanonical={bad}; snapshot_roundtrip=true; full_compile=Ok; N3_bad_cells={bad_cells:?}");
  let masks=pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
  let cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
  assert!(!cells.iter().any(|c|c.column==0&&c.row==444));
  assert_ne!(masks[444>>4]&(1<<(444&15)),0);
  let hiding_context=aspis_core::state_only_hiding::StateOnlyHidingContext::pool_v1_pair_forest_v1([13;32],[17;32]);
  let mut store=aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
  let material=aspis_prover::state_only_hiding::build_pool_v1_pair_forest_mask_material_v1(aspis_prover::HOST_HASH,[23;32],hiding_context,[19;32],&mut store).unwrap();
  let mut noised=compiled.semantic_c1.clone();
  let applied=aspis_prover::state_only_hiding::apply_pool_v1_pair_forest_mask_material_v1(&mut noised,material).unwrap();
  assert_eq!(noised.c1[0][444],compiled.semantic_c1.c1[0][444]);
  assert!(noised.c1.iter().all(|c|inactive_sum_m31(c,&masks)==M31::ZERO));
  assert!(applied.mask_only_c1.iter().all(|c|inactive_sum_m31(c,&masks)==M31::ZERO));
  let rejected=check_base_column(&noised.c1[0]).is_err();
  assert_eq!(rejected,bad);
  println!("native_mask_material=Ok; native_mask_apply=Ok; N4_c1_balanced=16; N4_mask_only_balanced=10; row444_active=true; row444_masked=false; N3_check_base_column_rejects={rejected}; honest_entropy=[19;32]; nonce=[17;32]");
  let actual_public=aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::Transfer(&public,&compiled.public_statement);
  let mut boundary=GuardBoundary::default();
  let g: &[QM31;1024]=applied.g.as_slice().try_into().unwrap();
  let h: &[QM31;1024]=applied.h1_padding.as_slice().try_into().unwrap();
  let checked=aspis_r1_cost_probe::host_semantic::build_with_material(actual_public,&compiled,&noised,&applied.mask_only_c1,&[QM31::ZERO;1024],g,h,&mut boundary,LegacyHashFn(aspis_prover::HOST_HASH),aspis_r1_cost_probe::transport::Variant::S2);
  assert!(matches!(checked,Err(aspis_r1_cost_probe::host_wire::Error::Public)));
  assert_eq!(boundary.c1_calls,if bad {0}else{1});
  println!("actual_native_build_with_material_c1_calls={}; expected_guard_rejects={bad}",boundary.c1_calls);
  if bad {
   let actual_public=aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::Transfer(&public,&compiled.public_statement);
   let full=aspis_r1_cost_probe::prover::prove_masked_fixture(actual_public,&compiled,aspis_r1_cost_probe::transport::Variant::S2,aspis_prover::HOST_HASH,&[29;32]);
   assert!(matches!(full,Err(aspis_r1_cost_probe::verifier::Error::Semantic)));
   println!("actual_prove_masked_fixture=Err(Semantic); variant=S2; fixture_seed=[29;32]");
   println!("PUBLIC={public:?}\nWITNESS={witness:?}\nSNAPSHOT={snapshot:?}\nSNAPSHOT_BYTES={bytes:?}");
   assert_eq!(compiled.semantic_c1.c1[0][27*16+12].0,P);
   assert!(!bad_cells.is_empty(),"counterexample must reach the actual noncanonical raw guard predicate");
  }else{assert!(bad_cells.is_empty());}
 }
}
