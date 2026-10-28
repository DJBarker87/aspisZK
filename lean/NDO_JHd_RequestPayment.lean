import NDO_JFs_PaymentDigests
import NDO_JFs_Cell04
import NDO_JFs_Cell05
import NDO_JFs_Cell06
import NDO_JFs_Cell07
import NDO_JHd_RequestCanon
set_option autoImplicit false
namespace AspisR1.JHd_RequestPayment
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.payment_relation

def common : CommonPublicV1 :=
  {pool:=JFs_Cell04.value,deployment_domain:=JFs_Cell05.value,
   anchor_sequence:=core.num.U64.from_le_bytes JFs_Cell06.value,
   anchor_root:=JFt_Digest43.value,nullifier:=JFt_Digest44.value,
   asset_id:=core.num.U32.from_le_bytes JFs_Cell07.value}

def value : PoolV1PrivateTransferPublicV1 :=
  {pool:=common.pool,deployment_domain:=common.deployment_domain,
   anchor_sequence:=common.anchor_sequence,anchor_root:=common.anchor_root,
   nullifier:=common.nullifier,asset_id:=common.asset_id,
   recipient_commitment:=JFt_Digest45.value,change_commitment:=JFt_Digest46.value}

theorem sequence : core.num.U64.from_le_bytes JFs_Cell06.value=42#u64 := by rfl
theorem asset : core.num.U32.from_le_bytes JFs_Cell07.value=77#u32 := by rfl

theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    JFs_Cell04.value (Array.repeat 32#usize 0#u8)=ok false := by rfl
theorem domain_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    JFs_Cell05.value (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem common_validated : validate_common common=ok (.Ok ()) := by
  unfold validate_common common
  simp only [pool_nonzero,domain_nonzero,bind_tc_ok,Bool.false_eq_true,↓reduceIte,sequence,asset,
    JHd_RequestCanon.source _ JFt_Digest43.canonical,
    JHd_RequestCanon.source _ JFt_Digest44.canonical]
  unfold pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY pool_v1.format.POOL_V1_TREE_DEPTH aspis_core.field.P
  rfl

theorem validated : validate_pool_v1_private_transfer_public_v1 value=ok (.Ok ()) := by
  unfold validate_pool_v1_private_transfer_public_v1
  have transfer : transfer_common value=ok common := by rfl
  rw [transfer,bind_tc_ok,common_validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    value,JHd_RequestCanon.source _ JFt_Digest45.canonical,
    JHd_RequestCanon.source _ JFt_Digest46.canonical,Bool.true_eq,↓reduceIte]

#print axioms sequence
#print axioms asset
#print axioms pool_nonzero
#print axioms domain_nonzero
#print axioms common_validated
#print axioms validated
end AspisR1.JHd_RequestPayment
