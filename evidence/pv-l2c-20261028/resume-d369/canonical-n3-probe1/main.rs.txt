use aspis_core::field::{M31,P};
use aspis_statement::{derive_owner_key,poseidon2::Digest,pool_v1::{*,pair_trace::PoolV1PairInputNoteWitnessV1,pair_forest_trace::*}};
fn digest(seed:u32)->Digest {core::array::from_fn(|i|M31(seed+17*i as u32+1))}
fn main() {
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
  if bad {recipient.owner_key[0]=M31(P);}
  let change=PoolV1OutputNoteWitnessV1 {owner_key:digest(500),salt:digest(600),value:400};
  let public=PoolV1PrivateTransferPublicV1 {pool:[1;32],deployment_domain:[5;32],anchor_sequence:42,anchor_root:anchor,nullifier:pool_v1_nullifier(&key,&salt),asset_id:asset,recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,recipient.value,asset,&recipient.salt),change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,asset,&change.salt)};
  let witness=PoolV1PairForestPrivateTransferWitnessV1 {input,recipient,change};
  let context=PoolV1PaymentRelationContextV1 {runtime_binding:PoolV1PaymentRuntimeBindingV1 {pool:public.pool,deployment_domain:public.deployment_domain,anchor_sequence:public.anchor_sequence,anchor_root:public.anchor_root,asset_id:public.asset_id},spent_nullifiers:&[]};
  let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,context,decoded).expect("canonical snapshot decode then full compiler success");
  let bad_cells:Vec<_>=compiled.semantic_c1.c1.iter().enumerate().flat_map(|(c,col)|col.iter().enumerate().filter_map(move |(r,x)|if x.0>=P {Some((c,r,x.0))}else{None})).collect();
  println!("case_noncanonical={bad}; snapshot_roundtrip=true; full_compile=Ok; N3_bad_cells={bad_cells:?}");
  if bad {
   println!("PUBLIC={public:?}\nWITNESS={witness:?}\nSNAPSHOT={snapshot:?}\nSNAPSHOT_BYTES={bytes:?}");
   assert_eq!(compiled.semantic_c1.c1[0][27*16+12].0,P);
   assert!(!bad_cells.is_empty(),"counterexample must reach the actual noncanonical raw guard predicate");
  }else{assert!(bad_cells.is_empty());}
 }
}
