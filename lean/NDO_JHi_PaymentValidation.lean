import NDO_JHi_DigestAssociation
import NDO_JFs_PaymentValue
set_option autoImplicit false
namespace AspisR1.JHi_PaymentValidation
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1.payment_relation

def common : CommonPublicV1 :=
  {pool:=JFs_PaymentValue.common.pool,deployment_domain:=JFs_PaymentValue.common.deployment_domain,
   anchor_sequence:=JFs_PaymentValue.common.anchor_sequence,anchor_root:=JFs_PaymentValue.common.anchor_root,
   nullifier:=JFs_PaymentValue.common.nullifier,asset_id:=JFs_PaymentValue.common.asset_id}

theorem common_validated : validate_common common=ok (.Ok ()) := by
  have pool : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      common.pool (Array.repeat 32#usize 0#u8)=ok false := JFs_PaymentValue.pool_nonzero
  have domain : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      common.deployment_domain (Array.repeat 32#usize 0#u8)=ok false := JFs_PaymentValue.domain_nonzero
  unfold validate_common
  dsimp only
  rw [pool,bind_tc_ok]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [domain,bind_tc_ok]
  simp only [Bool.false_eq_true,↓reduceIte]
  unfold common JFs_PaymentValue.common
  simp only [JFs_PaymentValue.pool_nonzero,JFs_PaymentValue.domain_nonzero,bind_tc_ok,
    Bool.false_eq_true,↓reduceIte,JFs_PaymentValue.sequence,JFs_PaymentValue.asset,
    JHi_DigestAssociation.canonical,JFs_PaymentCanon.source _ JFt_Digest43.canonical,
    JFs_PaymentCanon.source _ JFt_Digest44.canonical]
  unfold aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY
    aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH aspis_core.field.P
  rfl
#print axioms common_validated

theorem source : validate_pool_v1_private_transfer_public_v1 JHg_RawPrefix.payment=ok (.Ok ()) := by
  unfold validate_pool_v1_private_transfer_public_v1
  have transfer : transfer_common JHg_RawPrefix.payment=ok common := by rfl
  rw [transfer,bind_tc_ok,common_validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    JHi_DigestAssociation.canonical]
  change (do
    let b ← AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical JFt_Digest45.value
    if b then do
      let b1 ← AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical JFt_Digest46.value
      if b1 then ok (core.result.Result.Ok () : core.result.Result Unit PoolV1PaymentStatementFormatError) else ok (core.result.Result.Err .NonCanonicalDigest)
    else ok (core.result.Result.Err .NonCanonicalDigest)) = _
  simp only [JFs_PaymentCanon.source _ JFt_Digest45.canonical,
    JFs_PaymentCanon.source _ JFt_Digest46.canonical,bind_tc_ok,Bool.true_eq,↓reduceIte]
#print axioms source
end AspisR1.JHi_PaymentValidation
