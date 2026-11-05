import Lean
import NFY_Part036
import NFY_Part043
import NFY_Part040

-- BEGIN copied JHd_RequestCanon: lean/JHd_RequestCanon.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestCanon
open Aeneas Aeneas.Std Result WP
open AspisR20Request

theorem source (digest : Array U32 8#usize) (canon : NFY_JFu_DigestCanonical.Canonical digest) :
    pool_v1.payment_relation.digest_is_canonical digest=ok true := by
  have c0:=canon ⟨0,by decide⟩
  have c1:=canon ⟨1,by decide⟩
  have c2:=canon ⟨2,by decide⟩
  have c3:=canon ⟨3,by decide⟩
  have c4:=canon ⟨4,by decide⟩
  have c5:=canon ⟨5,by decide⟩
  have c6:=canon ⟨6,by decide⟩
  have c7:=canon ⟨7,by decide⟩
  have spec : pool_v1.payment_relation.digest_is_canonical digest ⦃ b => b=true ⦄ := by
    unfold pool_v1.payment_relation.digest_is_canonical
    step*
    all_goals unfold aspis_core.field.P at *
    all_goals simp_all [NFY_JFu_DigestCanonical.Canonical]
    all_goals scalar_tac
  obtain ⟨b,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end AspisR1.NFY_JHd_RequestCanon
-- END copied JHd_RequestCanon
-- BEGIN copied JHd_RequestPayment: lean/JHd_RequestPayment.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestPayment
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.payment_relation

def common : CommonPublicV1 :=
  {pool:=NFY_JFs_Cell04.value,deployment_domain:=NFY_JFs_Cell05.value,
   anchor_sequence:=core.num.U64.from_le_bytes NFY_JFs_Cell06.value,
   anchor_root:=NFY_JFt_Digest43.value,nullifier:=NFY_JFt_Digest44.value,
   asset_id:=core.num.U32.from_le_bytes NFY_JFs_Cell07.value}

def value : PoolV1PrivateTransferPublicV1 :=
  {pool:=common.pool,deployment_domain:=common.deployment_domain,
   anchor_sequence:=common.anchor_sequence,anchor_root:=common.anchor_root,
   nullifier:=common.nullifier,asset_id:=common.asset_id,
   recipient_commitment:=NFY_JFt_Digest45.value,change_commitment:=NFY_JFt_Digest46.value}

theorem sequence : core.num.U64.from_le_bytes NFY_JFs_Cell06.value=42#u64 := by rfl
theorem asset : core.num.U32.from_le_bytes NFY_JFs_Cell07.value=77#u32 := by rfl

theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    NFY_JFs_Cell04.value (Array.repeat 32#usize 0#u8)=ok false := by rfl
theorem domain_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    NFY_JFs_Cell05.value (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem common_validated : validate_common common=ok (.Ok ()) := by
  unfold validate_common common
  simp only [pool_nonzero,domain_nonzero,bind_tc_ok,Bool.false_eq_true,↓reduceIte,sequence,asset,
    NFY_JHd_RequestCanon.source _ NFY_JFt_Digest43.canonical,
    NFY_JHd_RequestCanon.source _ NFY_JFt_Digest44.canonical]
  unfold pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY pool_v1.format.POOL_V1_TREE_DEPTH aspis_core.field.P
  rfl

theorem validated : validate_pool_v1_private_transfer_public_v1 value=ok (.Ok ()) := by
  unfold validate_pool_v1_private_transfer_public_v1
  have transfer : transfer_common value=ok common := by rfl
  rw [transfer,bind_tc_ok,common_validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    value,NFY_JHd_RequestCanon.source _ NFY_JFt_Digest45.canonical,
    NFY_JHd_RequestCanon.source _ NFY_JFt_Digest46.canonical,Bool.true_eq,↓reduceIte]

#print axioms sequence
#print axioms asset
#print axioms pool_nonzero
#print axioms domain_nonzero
#print axioms common_validated
#print axioms validated
end AspisR1.NFY_JHd_RequestPayment
-- END copied JHd_RequestPayment
-- BEGIN copied JHd_RequestDigests: lean/JHd_RequestDigests.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestDigests
open Aeneas Aeneas.Std Result
theorem decode43 : AspisR20Request.atomic_statement.decode_digest_canonical
    NFY_JFs_PaymentDigests.bytes43=ok (.Ok NFY_JFt_Digest43.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode43
theorem decode44 : AspisR20Request.atomic_statement.decode_digest_canonical
    NFY_JFs_PaymentDigests.bytes44=ok (.Ok NFY_JFt_Digest44.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode44
theorem decode45 : AspisR20Request.atomic_statement.decode_digest_canonical
    NFY_JFs_PaymentDigests.bytes45=ok (.Ok NFY_JFt_Digest45.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode45
theorem decode46 : AspisR20Request.atomic_statement.decode_digest_canonical
    NFY_JFs_PaymentDigests.bytes46=ok (.Ok NFY_JFt_Digest46.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode46
end AspisR1.NFY_JHd_RequestDigests
-- END copied JHd_RequestDigests

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
