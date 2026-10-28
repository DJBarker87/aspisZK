use super::*;
fn digest() -> Digest { [M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())] }
fn canon(d:&Digest)->bool {d[0].0<P&&d[1].0<P&&d[2].0<P&&d[3].0<P&&d[4].0<P&&d[5].0<P&&d[6].0<P&&d[7].0<P}
fn common()->CommonPublicV1 {CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any())}}
fn common_spec(c:CommonPublicV1)->Result<(),PoolV1PaymentStatementFormatError>{
 use PoolV1PaymentStatementFormatError::*;
 if c.pool==[0;32]||c.deployment_domain==[0;32]{Err(ZeroRequiredBinding)}
 else if c.anchor_sequence>POOL_V1_LEAF_CAPACITY{Err(InvalidAnchorSequence)}
 else if !canon(&c.anchor_root)||!canon(&c.nullifier){Err(NonCanonicalDigest)}
 else if c.asset_id.0>=P{Err(NonCanonicalAssetId)}else{Ok(())}
}
fn transfer()->PoolV1PrivateTransferPublicV1 {let c=common();PoolV1PrivateTransferPublicV1{pool:c.pool,deployment_domain:c.deployment_domain,anchor_sequence:c.anchor_sequence,anchor_root:c.anchor_root,nullifier:c.nullifier,asset_id:c.asset_id,recipient_commitment:digest(),change_commitment:digest()}}
fn withdrawal()->PoolV1WithdrawalPublicV1 {let c=common();PoolV1WithdrawalPublicV1{pool:c.pool,deployment_domain:c.deployment_domain,anchor_sequence:c.anchor_sequence,anchor_root:c.anchor_root,nullifier:c.nullifier,asset_id:c.asset_id,amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()}}
#[kani::proof]
fn NBG_digest_canonical(){let d=digest();assert!(super::digest_is_canonical(&d)==canon(&d));kani::cover!(d[0].0==P);}
#[kani::proof]
fn NBG_common_validation(){let c=common();assert!(super::validate_common(c)==common_spec(c));kani::cover!(c.pool==[0;32]);}
#[kani::proof]
fn NBG_transfer_validation(){
 let p=transfer();let c=super::transfer_common(&p);let expect=common_spec(c).and_then(|()|if !canon(&p.recipient_commitment)||!canon(&p.change_commitment){Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest)}else{Ok(())});
 assert!(super::validate_pool_v1_private_transfer_public_v1(&p)==expect);kani::cover!(p.asset_id.0==P);
}
#[kani::proof]
fn NBG_withdrawal_validation(){
 let p=withdrawal();let expect=common_spec(super::withdrawal_common(&p)).and_then(|()|{
 use PoolV1PaymentStatementFormatError::*;
 if p.amount==0||p.amount>=VALUE_LIMIT{Err(InvalidWithdrawalAmount)}else if p.destination_token_account==[0;32]{Err(InvalidDestination)}else if !canon(&p.change_commitment){Err(NonCanonicalDigest)}else{Ok(())}});
 assert!(super::validate_pool_v1_withdrawal_public_v1(&p)==expect);kani::cover!(p.amount==0);
}
#[kani::proof]
fn NBG_projections(){
 let t=transfer();let w=withdrawal();let a=super::transfer_common(&t);let b=super::withdrawal_common(&w);
 let i:usize=kani::any();kani::assume(i<32);let j:usize=kani::any();kani::assume(j<8);
 assert!(a.pool[i]==t.pool[i]&&a.deployment_domain[i]==t.deployment_domain[i]);assert!(a.anchor_sequence==t.anchor_sequence);assert!(a.anchor_root[j].0==t.anchor_root[j].0&&a.nullifier[j].0==t.nullifier[j].0&&a.asset_id.0==t.asset_id.0);
 assert!(b.pool[i]==w.pool[i]&&b.deployment_domain[i]==w.deployment_domain[i]);assert!(b.anchor_sequence==w.anchor_sequence);assert!(b.anchor_root[j].0==w.anchor_root[j].0&&b.nullifier[j].0==w.nullifier[j].0&&b.asset_id.0==w.asset_id.0);
 kani::cover!(a.asset_id.0==u32::MAX);
}
#[kani::proof]
fn NBG_header(){
 let bytes:[u8;POOL_V1_PAYMENT_STATEMENT_BYTES]=kani::any();let magic:[u8;4]=kani::any();let v:bool=kani::any();let kind=if v{PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};
 use PoolV1PaymentStatementFormatError::*;
 let expect=if bytes[0]!=magic[0]||bytes[1]!=magic[1]||bytes[2]!=magic[2]||bytes[3]!=magic[3]{Err(WrongMagic)}
 else if bytes[4]!=POOL_V1_PAYMENT_STATEMENT_VERSION{Err(WrongVersion)}else if bytes[5]!=kind as u8{Err(WrongTransitionKind)}else if bytes[6]!=POOL_V1_DIGEST_ENCODING_VERSION{Err(WrongDigestEncoding)}else if bytes[7]!=0{Err(NonZeroReserved)}else{Ok(())};
 assert!(super::require_header(&bytes,magic,kind)==expect);kani::cover!(expect==Ok(()));
}
