from pathlib import Path
import sys
sys.dont_write_bytecode=True
from NBP_patch_sources import added_patch,pieces
import difflib
E=Path(__file__).resolve().parent
old=added_patch(E/'NBP_statement.patch','/NBP_codecs.rs')+added_patch(E/'NBP_statement2.patch','/NBP_codecs.rs')
s='''fn NBP_t()->PoolV1PrivateTransferPublicV1 { PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NBP_digest(),nullifier:NBP_digest(),asset_id:M31(kani::any()),recipient_commitment:NBP_digest(),change_commitment:NBP_digest()} }
fn NBP_w()->PoolV1WithdrawalPublicV1 { PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NBP_digest(),nullifier:NBP_digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:NBP_digest()} }
fn NBP_encoded_common_byte(c:CommonPublicV1,withdrawal:bool,j:usize)->u8 {
 match j {0=>65,1=>83,2=>if withdrawal{87}else{67},3=>80,4=>1,5=>if withdrawal{2}else{1},6=>1,7=>0,
 8..=39=>c.pool[j-8],40..=71=>c.deployment_domain[j-40],72..=79=>c.anchor_sequence.to_le_bytes()[j-72],80..=111=>NBP_digest_bytes(&c.anchor_root)[j-80],112..=143=>NBP_digest_bytes(&c.nullifier)[j-112],144..=147=>c.asset_id.0.to_le_bytes()[j-144],_=>0}
}
#[kani::proof]
#[kani::unwind(256)]
#[kani::stub(crate::atomic_statement::encode_digest_canonical,NBP_digest_bytes)]
fn NBP_transfer_encoder() {
 let p=NBP_t();let j:usize=kani::any();kani::assume(j<216);
 match (super::encode_pool_v1_private_transfer_public_v1(&p),super::validate_pool_v1_private_transfer_public_v1(&p)) {
 (Err(a),Err(e))=>assert!(a==e),(Ok(b),Ok(()))=>{
 let v=if j<152{NBP_encoded_common_byte(super::transfer_common(&p),false,j)}else if j<184{NBP_digest_bytes(&p.recipient_commitment)[j-152]}else{NBP_digest_bytes(&p.change_commitment)[j-184]};assert!(b[j]==v);
 },_=>assert!(false)}
 kani::cover!(p.pool[0]==0);
}
#[kani::proof]
#[kani::unwind(256)]
#[kani::stub(crate::atomic_statement::encode_digest_canonical,NBP_digest_bytes)]
fn NBP_withdrawal_encoder() {
 let p=NBP_w();let j:usize=kani::any();kani::assume(j<216);
 match (super::encode_pool_v1_withdrawal_public_v1(&p),super::validate_pool_v1_withdrawal_public_v1(&p)) {
 (Err(a),Err(e))=>assert!(a==e),(Ok(b),Ok(()))=>{
 let v=if j<148{NBP_encoded_common_byte(super::withdrawal_common(&p),true,j)}else if j<152{p.amount.to_le_bytes()[j-148]}else if j<184{p.destination_token_account[j-152]}else{NBP_digest_bytes(&p.change_commitment)[j-184]};assert!(b[j]==v);
 },_=>assert!(false)}
 kani::cover!(p.amount==0);
}
fn NBP_transfer_spec(b:&[u8;216])->Result<PoolV1PrivateTransferPublicV1,PoolV1PaymentStatementFormatError> {
 super::require_header(b,*b"ASCP",PoolV1TransitionKind::PrivateTransfer)?;
 if b[148]!=0||b[149]!=0||b[150]!=0||b[151]!=0{return Err(PoolV1PaymentStatementFormatError::NonZeroReserved)}
 let c=NBP_common_spec(b)?;
 let r=crate::atomic_statement::decode_digest_canonical(&NBP_raw32(b,152)).map_err(|_|PoolV1PaymentStatementFormatError::NonCanonicalDigest)?;
 let z=crate::atomic_statement::decode_digest_canonical(&NBP_raw32(b,184)).map_err(|_|PoolV1PaymentStatementFormatError::NonCanonicalDigest)?;
 let p=PoolV1PrivateTransferPublicV1{pool:c.pool,deployment_domain:c.deployment_domain,anchor_sequence:c.anchor_sequence,anchor_root:c.anchor_root,nullifier:c.nullifier,asset_id:c.asset_id,recipient_commitment:r,change_commitment:z};
 super::validate_pool_v1_private_transfer_public_v1(&p)?;Ok(p)
}
fn NBP_withdrawal_spec(b:&[u8;216])->Result<PoolV1WithdrawalPublicV1,PoolV1PaymentStatementFormatError> {
 super::require_header(b,*b"ASWP",PoolV1TransitionKind::Withdrawal)?;
 let c=NBP_common_spec(b)?;
 let z=crate::atomic_statement::decode_digest_canonical(&NBP_raw32(b,184)).map_err(|_|PoolV1PaymentStatementFormatError::NonCanonicalDigest)?;
 let p=PoolV1WithdrawalPublicV1{pool:c.pool,deployment_domain:c.deployment_domain,anchor_sequence:c.anchor_sequence,anchor_root:c.anchor_root,nullifier:c.nullifier,asset_id:c.asset_id,amount:u32::from_le_bytes([b[148],b[149],b[150],b[151]]),destination_token_account:NBP_raw32(b,152),change_commitment:z};
 super::validate_pool_v1_withdrawal_public_v1(&p)?;Ok(p)
}
#[kani::proof]
#[kani::unwind(256)]
fn NBP_transfer_decoder() {
 let b:[u8;216]=kani::any();assert!(super::decode_pool_v1_private_transfer_public_v1(&b)==NBP_transfer_spec(&b));kani::cover!(b[0]==0);
}
#[kani::proof]
#[kani::unwind(256)]
fn NBP_withdrawal_decoder() {
 let b:[u8;216]=kani::any();assert!(super::decode_pool_v1_withdrawal_public_v1(&b)==NBP_withdrawal_spec(&b));kani::cover!(b[0]==0);
}
'''
p='crates/aspis-statement/src/pool_v1/payment_relation/NBP_codecs.rs'
(E/'NBP_payments.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+s).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
