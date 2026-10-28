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
