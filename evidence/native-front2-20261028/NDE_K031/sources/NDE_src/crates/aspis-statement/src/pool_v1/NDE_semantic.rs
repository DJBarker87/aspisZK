use super::*;
#[path="NDE_reference.rs"] pub(super) mod reference;
pub(super) fn to_ref(v:QM31)->reference::Q { reference::Q { c0:reference::C{a:v.c0.a.0,b:v.c0.b.0},c1:reference::C{a:v.c1.a.0,b:v.c1.b.0} } }
pub(super) fn to_native(v:reference::Q)->QM31 {QM31 {c0:CM31{a:M31(v.c0.a),b:M31(v.c0.b)},c1:CM31{a:M31(v.c1.a),b:M31(v.c1.b)}}}
#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::lift_m31)]
fn NDE_contract(){let v:u32=kani::any();let _=super::lift_m31(M31(v));}
pub(super) fn canonical(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
pub(super) fn native_initial(v:CompiledVariant,a:QM31,b:QM31,c:QM31)->(QM31,QM31,QM31,QM31){let r=reference::initial_ref(v==CompiledVariant::Withdrawal,to_ref(a),to_ref(b),to_ref(c));(to_native(r.0),to_native(r.1),to_native(r.2),to_native(r.3))}
pub(super) fn native_scalar(v:CompiledVariant,p:bool,i:QM31,o:QM31,t:QM31,w:QM31)->[QM31;2]{let r=reference::scalar_ref(v==CompiledVariant::Withdrawal,p,to_ref(i),to_ref(o),to_ref(t),to_ref(w));[to_native(r[0]),to_native(r[1])]}
fn anyq()->QM31{let a:[u32;4]=kani::any();to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}})}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::initial_variant_selectors)]
fn NDE_initial(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let a=anyq();let b=anyq();let c=anyq();kani::assume(canonical(a)&&canonical(b)&&canonical(c));let _=super::initial_variant_selectors(v,a,b,c);}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::scalar_lanes)]
fn NDE_scalar(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let p:bool=kani::any();let i=anyq();let o=anyq();let t=anyq();let w=anyq();kani::assume(canonical(o)&&canonical(t)&&canonical(w));let _=super::scalar_lanes(v,p,i,o,t,w);}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::copy_variant)]
fn NDE_variant(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let _=super::copy_variant(v);}
#[path="NDE_claim_reference.rs"] pub(super) mod claim_reference;
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(85)]
#[kani::proof_for_contract(super::selected_claim)]
fn NDE_claim(){
 // QM31, CM31 and M31 are transparent records of u32. Every bit pattern is
 // a valid Rust carrier; canonicality is unnecessary for a projection.
 let raw:[[u32;4];84]=kani::any();
 let claims=raw.map(|a|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}}));
 let p:usize=kani::any();let c:usize=kani::any();kani::assume(p<3&&c<28);
 let _=super::selected_claim(&claims,p,c);
}
#[cfg(NDE_carry_step)] pub(super) static mut NDE_CARRY:usize=0;
#[cfg(NDE_carry_step)] pub(super) static mut NDE_NEXT_INDEX:u64=0;
#[cfg(NDE_carry_step)] pub(super) static mut NDE_CONTINUE:bool=false;
#[cfg(NDE_carry_step)] pub(super) fn carry_record(index:u64){unsafe{NDE_NEXT_INDEX=index;NDE_CONTINUE=true;}}
#[cfg(NDE_carry_step)]
#[kani::proof]
#[kani::unwind(2)]
fn NDE_carry_step(){
 let index:u64=kani::any();let carry:usize=kani::any();
 unsafe{NDE_CARRY=carry;NDE_NEXT_INDEX=index;NDE_CONTINUE=false;}
 let result=super::bounded_append_carry(index);
 let step=unsafe{(NDE_NEXT_INDEX,result,NDE_CONTINUE)};
 assert!((step==reference::carry_step_ref(index,carry)) != cfg!(NDE_invert));
}
pub(super) static mut NDE_PUBLIC_INDEX:usize=0;
pub(super) fn same_public(r:&SemanticPublic<'_>,q:reference::PublicRef<'_,[u8;32],Digest,M31,PoolV1PairLatePublicStatementV1>)->bool{
 let j=unsafe{NDE_PUBLIC_INDEX};let k=j&7;
 let recipient=match(r.recipient,q.recipient){(None,None)=>true,(Some(a),Some(b))=>a[k]==b[k],_=>false};
 r.variant==if q.withdraw{CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer}
 && r.pool[j]==q.pool[j] && r.deployment_domain[j]==q.domain[j] && r.anchor[k]==q.anchor[k]
 && r.nullifier[k]==q.nullifier[k] && r.asset_id==q.asset && recipient
 && r.change[k]==q.change[k] && r.withdrawal_amount==q.amount && core::ptr::eq(r.transition,q.transition)
}
pub(super) fn private_matches(r:&SemanticPublic<'_>,p:&PoolV1PrivateTransferPublicV1,t:&PoolV1PairLatePublicStatementV1)->bool{
 same_public(r,reference::private_public_ref(reference::PrivateInput{pool:p.pool,domain:p.deployment_domain,anchor:p.anchor_root,nullifier:p.nullifier,asset:p.asset_id,recipient:p.recipient_commitment,change:p.change_commitment},t))
}
pub(super) fn withdrawal_matches(r:&SemanticPublic<'_>,p:&PoolV1WithdrawalPublicV1,t:&PoolV1PairLatePublicStatementV1)->bool{
 same_public(r,reference::withdrawal_public_ref(reference::WithdrawalInput{pool:p.pool,domain:p.deployment_domain,anchor:p.anchor_root,nullifier:p.nullifier,asset:p.asset_id,amount:p.amount,change:p.change_commitment},t))
}
fn any_digest()->Digest{let a:[u32;8]=kani::any();a.map(M31)}
fn any_transition()->PoolV1PairLatePublicStatementV1{
 PoolV1PairLatePublicStatementV1{
  live_snapshot:crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:any_digest(),frontier:core::array::from_fn(|_|any_digest())},
  candidate_afterstate:crate::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:any_digest(),next_frontier:core::array::from_fn(|_|any_digest())}
 }
}
#[kani::unwind(22)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::private_public)]
fn NDE_private_public(){
 let p=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:any_digest(),nullifier:any_digest(),asset_id:M31(kani::any()),recipient_commitment:any_digest(),change_commitment:any_digest()};
 let t=any_transition();let j:usize=kani::any();kani::assume(j<32);unsafe{NDE_PUBLIC_INDEX=j;}let _=super::private_public(&p,&t);
}
#[kani::unwind(22)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::withdrawal_public)]
fn NDE_withdrawal_public(){
 let p=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:any_digest(),nullifier:any_digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:any_digest()};
 let t=any_transition();let j:usize=kani::any();kani::assume(j<32);unsafe{NDE_PUBLIC_INDEX=j;}let _=super::withdrawal_public(&p,&t);
}
