use super::*;
use aspis_core::state_only_hiding::state_only_explicit_g_mask_factor;
#[path="r12_data.rs"] mod r12_data;
fn r12_point(prefix:&[QM31],t:QM31,assignment:usize)->[QM31;10]{let j=prefix.len();let mut z=[QM31::ZERO;10];z[..j].copy_from_slice(prefix);z[j]=t;for k in j+1..10{z[k]=lift(((assignment>>(9-k))&1)as u32);}z}
fn r12_g_claims(c1:&[Vec<M31>;16],g:&[QM31;ROWS],z:&[QM31;10])->[QM31;POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1]{let mut out=claims(c1,&[QM31::ZERO;ROWS],z);for(i,p)in[*z,successor_point(z),xor12_point(z)].iter().enumerate(){out[i*28+27]=multilinear_evaluate_qm31(g,p).unwrap();}out}
#[test]
fn r12_complete_selected_terminal_preserves_earlier_rounds(){
 let pool=[0x31;32];let domain=[0x73;32];let prepared=prepare_v7_pair_forest_transfer_fixture_v1(pool,[0x32;32],[0x33;32],0,domain,source_snapshot(pool,domain)).unwrap();
 let context=PoolV1PaymentRelationContextV1{runtime_binding:PoolV1PaymentRuntimeBindingV1{pool:prepared.public.pool,deployment_domain:prepared.public.deployment_domain,anchor_sequence:prepared.public.anchor_sequence,anchor_root:prepared.public.anchor_root,asset_id:prepared.public.asset_id},spent_nullifiers:&[]};
 let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&prepared.public,&prepared.witness,context,prepared.transition.live_snapshot).unwrap();
 let prefix=[lift(19),QM31{c0:CM31::new(M31(23),M31(2)),c1:CM31::new(M31(3),M31(5))}];let zero_point=core::array::from_fn(|i|lift(41+i as u32));let zero=[QM31::ZERO;ROWS];
 for j in[1usize,2]{let mut g=[QM31::ZERO;ROWS];for k in[0usize,13,26]{let pairs:Vec<_>=if j==1{r12_data::PAIRS_R1[k].to_vec()}else{r12_data::PAIRS_R2[k].to_vec()};for[r,s]in pairs{g[r]=g[r].add(lift(k as u32+1));g[s]=g[s].sub(lift(k as u32+1));}}
  assert_eq!(inactive_rows().iter().fold(QM31::ZERO,|s,&r|s.add(g[r])),QM31::ZERO);
  for round in 0..=j{let mut actual=vec![QM31::ZERO;28];let mut expected=vec![QM31::ZERO;28];for t in 0..28{for b in 0..(1usize<<(9-round)){let p=r12_point(&prefix[..round],lift(t as u32),b);let before=evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(&prepared.public,&compiled.public_statement,&r12_g_claims(&compiled.semantic_c1.c1,&zero,&p),&p,lift(19),lift(23),lift(29),&zero_point,lift(31),lift(37)).unwrap();let after=evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(&prepared.public,&compiled.public_statement,&r12_g_claims(&compiled.semantic_c1.c1,&g,&p),&p,lift(19),lift(23),lift(29),&zero_point,lift(31),lift(37)).unwrap();actual[t]=actual[t].add(after.sub(before));expected[t]=expected[t].add(state_only_explicit_g_mask_factor(&p).mul(multilinear_evaluate_qm31(&g,&p).unwrap()));}}
   assert_eq!(actual,expected);if round<j{assert!(actual.iter().all(|x|*x==QM31::ZERO));}else{assert_eq!(actual[0].add(actual[1]),QM31::ZERO);assert!(interpolate(&actual).iter().any(|x|*x!=QM31::ZERO));}}
 }
}
