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

#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_reconstruct_step(){
 let view:[QM31;16]=core::array::from_fn(|_|canonical_q());let acc=canonical_q();let index:usize=kani::any();kani::assume(index<=9);
 if cfg!(NHG_invert){kani::assume(index>0);}
 let mut iter=view[..index].iter();let part=iter.next_back();let out=match part{None=>acc,Some(bit)=>acc.add(acc).add(*bit)};let limb:usize=kani::any();kani::assume(limb<4);
 let next=if index==0{0}else{index-1};assert_eq!(iter.len(),next);assert_eq!(iter.as_slice().as_ptr(),view.as_ptr());
 let expected=if index==0{q_words(acc)[limb]}else{word_add(word_add(q_words(acc)[limb],q_words(acc)[limb]),q_words(view[index-1])[limb])};
 assert_eq!(q_words(out)[limb],expected^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_initial_selectors(){
 let high27=canonical_q();let high28=canonical_q();let high29=canonical_q();let withdrawal:bool=kani::any();let v=if withdrawal{CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};
 let got=super::super::initial_variant_selectors(v,high27,high28,high29);let values=[got.0,got.1,got.2,got.3];let slot:usize=kani::any();kani::assume(slot<4);let limb:usize=kani::any();kani::assume(limb<4);
 if cfg!(NHG_invert){kani::assume(!withdrawal&&slot==0);}
 let a=q_words(high27)[limb];let b=q_words(high28)[limb];let c=q_words(high29)[limb];let expected=if withdrawal{if slot==1{word_add(word_add(a,b),c)}else{0}}else{match slot{0=>a,1=>0,2=>word_add(a,b),_=>c}};
 assert_eq!(q_words(values[slot])[limb],expected^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_sum_high_step(){
 let selectors=Selectors{high:core::array::from_fn(|_|canonical_q()),low:core::array::from_fn(|_|canonical_q())};let sum=canonical_q();let block:usize=kani::any();kani::assume(block<64);
 let out=sum.add(selectors.high[block]);let limb:usize=kani::any();kani::assume(limb<4);let expected=word_add(q_words(sum)[limb],q_words(selectors.high[block])[limb]);
 assert_eq!(q_words(out)[limb],expected^if cfg!(NHG_invert){1}else{0});
}
fn word_sub(a:u32,b:u32)->u32{if a>=b{a-b}else{2147483647+a-b}}
struct MulLog{calls:usize,left:[QM31;2],right:[QM31;2],reply:[QM31;2]}
fn mul_log(a:QM31,b:QM31,log:&mut MulLog)->QM31{
 assert!(q_words(a).iter().all(|&x|x<2147483647));assert!(q_words(b).iter().all(|&x|x<2147483647));let j=log.calls;assert!(j<2);log.calls+=1;log.left[j]=a;log.right[j]=b;log.reply[j]
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_equality_factor(){
 let a=canonical_q();let b=canonical_q();let reply=canonical_q();let mut log=MulLog{calls:0,left:[QM31::ZERO;2],right:[QM31::ZERO;2],reply:[reply,QM31::ZERO]};
 let ab=mul_log(a,b,&mut log);let out=QM31::ONE.sub(a).sub(b).add(ab).add(ab);let limb:usize=kani::any();kani::assume(limb<4);
 let expected=word_add(word_add(word_sub(word_sub(if limb==0{1}else{0},q_words(a)[limb]),q_words(b)[limb]),q_words(reply)[limb]),q_words(reply)[limb]);
 assert_eq!(log.calls,1);assert_eq!(q_words(log.left[0])[limb],q_words(a)[limb]);assert_eq!(q_words(log.right[0])[limb],q_words(b)[limb]);
 assert_eq!(q_words(out)[limb],expected^if cfg!(NHG_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_equality_step(){
 let left:[QM31;10]=core::array::from_fn(|_|canonical_q());let right:[QM31;10]=core::array::from_fn(|_|canonical_q());let index:usize=kani::any();kani::assume(index>=1&&index<=10);let product=canonical_q();let ab=canonical_q();let after=canonical_q();
 if cfg!(NHG_invert){kani::assume(index<10);}
 let mut log=MulLog{calls:0,left:[QM31::ZERO;2],right:[QM31::ZERO;2],reply:[ab,after]};
 let (out,next)=if index<10{let ab=mul_log(left[index],right[index],&mut log);let factor=QM31::ONE.sub(left[index]).sub(right[index]).add(ab).add(ab);(mul_log(product,factor,&mut log),index+1)}else{(product,index)};
 let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(next,if index<10{index+1}else{10});assert_eq!(log.calls,if index<10{2}else{0});
 if index<10{assert_eq!(q_words(log.left[0])[limb],q_words(left[index])[limb]);assert_eq!(q_words(log.right[0])[limb],q_words(right[index])[limb]^if cfg!(NHG_invert){1}else{0});assert_eq!(q_words(log.left[1])[limb],q_words(product)[limb]);}
 assert_eq!(q_words(out)[limb],q_words(if index<10{after}else{product})[limb]);
}

#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_sum_outer_step(){
 let r0s:usize=kani::any();let r0e:usize=kani::any();let r1s:usize=kani::any();let r1e:usize=kani::any();kani::assume(r0s<=r0e&&r0e<=64&&r1s<=r1e&&r1e<=64);let ranges=[r0s..r0e,r1s..r1e];let position:usize=kani::any();kani::assume(position<=2);let before=canonical_q();let reply=canonical_q();let mut iter=ranges[position..].iter();let part=iter.next();let mut calls=0;let mut start=0;let mut end=0;let out=match part{None=>before,Some(range)=>{let copied=range.clone();start=copied.start;end=copied.end;calls+=1;reply}};
 if cfg!(NHG_invert){kani::assume(position<2);}
 let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(iter.len(),2-position-if position<2{1}else{0});assert_eq!(calls,if position<2{1}else{0});
 if position<2{assert_eq!(start,ranges[position].start);assert_eq!(end,ranges[position].end^if cfg!(NHG_invert){1}else{0});}assert_eq!(q_words(out)[limb],q_words(if position<2{reply}else{before})[limb]);
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_reconstruct_seed(){let view:[QM31;16]=core::array::from_fn(|_|raw_q());let seed=view[9];let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(q_words(seed)[limb],q_words(view[9])[limb]^if cfg!(NHG_invert){1}else{0});}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_equality_seed(){
 let left:[QM31;10]=core::array::from_fn(|_|canonical_q());let right:[QM31;10]=core::array::from_fn(|_|canonical_q());let reply=canonical_q();let mut log=MulLog{calls:0,left:[QM31::ZERO;2],right:[QM31::ZERO;2],reply:[reply,QM31::ZERO]};let ab=mul_log(left[0],right[0],&mut log);let seed=QM31::ONE.sub(left[0]).sub(right[0]).add(ab).add(ab);let index=1usize;let limb:usize=kani::any();kani::assume(limb<4);
 assert_eq!(index,1);assert_eq!(log.calls,1);assert_eq!(q_words(log.left[0])[limb],q_words(left[0])[limb]);assert_eq!(q_words(log.right[0])[limb],q_words(right[0])[limb]^if cfg!(NHG_invert){1}else{0});
 let expected=word_add(word_add(word_sub(word_sub(if limb==0{1}else{0},q_words(left[0])[limb]),q_words(right[0])[limb]),q_words(reply)[limb]),q_words(reply)[limb]);assert_eq!(q_words(seed)[limb],expected);
}
