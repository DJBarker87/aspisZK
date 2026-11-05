use super::*;
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
#[kani::proof] #[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::pool_v1::pair_forest_semantic_terminal::r0::NHG_semantic::KMX_copy_nonoverlapping)]
fn NHG_semantic_source(){
 let p=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()};
 let w=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()};
 // Fully arbitrary typed transition: no zero/sparse prestate restriction.
 let t=PoolV1PairLatePublicStatementV1{
  live_snapshot:crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{
   pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:core::array::from_fn(|_|digest())},
  candidate_afterstate:crate::pool_v1::PoolV1PairVerifiedAfterstateV1{
   next_pair_index:kani::any(),next_root:digest(),next_frontier:core::array::from_fn(|_|digest())}};
 let withdrawal:bool=kani::any();let public=if withdrawal{Public::Withdrawal(&w,&t)}else{Public::Transfer(&p,&t)};
 let result=public.semantic();let j:usize=kani::any();kani::assume(j<8);let b:usize=kani::any();kani::assume(b<32);
 assert!(core::ptr::eq(result.transition,&t));
 let good=if withdrawal {
  matches!(result.variant,CompiledVariant::Withdrawal)&&result.pool[b]==w.pool[b]&&result.deployment_domain[b]==w.deployment_domain[b]&&result.anchor[j].0==(w.anchor_root[j].0 ^ if cfg!(NHG_invert){1}else{0})&&result.nullifier[j]==w.nullifier[j]&&result.asset_id==w.asset_id&&result.recipient.is_none()&&result.change[j]==w.change_commitment[j]&&result.withdrawal_amount==Some(w.amount)
 }else{
  matches!(result.variant,CompiledVariant::PrivateTransfer)&&result.pool[b]==p.pool[b]&&result.deployment_domain[b]==p.deployment_domain[b]&&result.anchor[j].0==(p.anchor_root[j].0 ^ if cfg!(NHG_invert){1}else{0})&&result.nullifier[j]==p.nullifier[j]&&result.asset_id==p.asset_id&&result.recipient.unwrap()[j]==p.recipient_commitment[j]&&result.change[j]==p.change_commitment[j]&&result.withdrawal_amount.is_none()
 };
 assert!(good);
}
// Exact KMX patch, unchanged. This file defines no substitute copy operation.
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));

fn raw_q()->QM31{let w:[u32;4]=kani::any();QM31{c0:CM31::new(M31(w[0]),M31(w[1])),c1:CM31::new(M31(w[2]),M31(w[3]))}}
fn q_words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_selected_claim(){
 let claims:[QM31;84]=core::array::from_fn(|_|raw_q());let point:usize=kani::any();kani::assume(point<3);let column:usize=kani::any();kani::assume(column<28);let limb:usize=kani::any();kani::assume(limb<4);
 let out=super::super::selected_claim(&claims,point,column);assert_eq!(q_words(out)[limb],q_words(claims[point*28+column])[limb]^if cfg!(NHG_invert){1}else{0});
}

fn canonical_q()->QM31{let w:[u32;4]=kani::any();kani::assume(w.iter().all(|&v|v<2147483647));QM31{c0:CM31::new(M31(w[0]),M31(w[1])),c1:CM31::new(M31(w[2]),M31(w[3]))}}
fn word_add(a:u32,b:u32)->u32{let sum=a+b;if sum>=2147483647{sum-2147483647}else{sum}}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_scalar_lanes(){
 let asset=raw_q();let output=canonical_q();let private=canonical_q();let withdrawal=canonical_q();let variant:bool=kani::any();let present:bool=kani::any();let v=if variant{CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};
 let got=super::super::scalar_lanes(v,present,asset,output,private,withdrawal);let lane:usize=kani::any();kani::assume(lane<2);let limb:usize=kani::any();kani::assume(limb<4);
 if cfg!(NHG_invert){kani::assume(lane==0);}
 let expected=if lane==0{q_words(asset)[limb]}else if !variant{word_add(q_words(output)[limb],q_words(private)[limb])}else if present{word_add(q_words(output)[limb],q_words(withdrawal)[limb])}else{q_words(output)[limb]};
 assert_eq!(q_words(got[lane])[limb],expected^if cfg!(NHG_invert){1}else{0});
}
fn NHG_carry_body(mut index:u64,mut carry:usize)->(bool,u64,usize){
 if carry<20{
  if index&1==0{return(true,index,carry)}
  index>>=1u32;
  carry+=1;
  (false,index,carry)
 }else{(true,index,carry)}
}
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_carry_step(){
 let index:u64=kani::any();let carry:usize=kani::any();kani::assume(carry<=20);let got=NHG_carry_body(index,carry);let done=carry==20||index&1==0;
 assert_eq!(got.0,done);assert_eq!(got.1,if done{index}else{index>>1});assert_eq!(got.2,(if done{carry}else{carry+1})^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(32)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_empty_root(){
 let level:usize=kani::any();kani::assume(level<21);let limb:usize=kani::any();kani::assume(limb<8);
 let got=super::super::empty_root(level);assert_eq!(got[limb].0,constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level][limb]^if cfg!(NHG_invert){1}else{0});
}
