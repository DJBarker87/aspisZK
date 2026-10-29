import NED_DigestCohorts
import NED_ReconstructCarriers
import NBG_PaymentValidators
set_option autoImplicit false
noncomputable section
namespace NED_PaymentCohorts
open Aeneas Aeneas.Std Result
abbrev T := NBN_ValidatorSummary.Transfer
abbrev W := NBN_ValidatorSummary.Withdrawal
abbrev C := NBG_PaymentChecks.C
abbrev RT := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev RW := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev RC := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.CommonPublicV1

def toRawTransfer (p : T) : RT := AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PrivateTransferPublicV1 p)
def toRawWithdrawal (p : W) : RW := AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1WithdrawalPublicV1 p)
def toRawCommon (c : C) : RC :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id⟩

theorem transfer_common (p : T) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.transfer_common (toRawTransfer p) =
    ok (toRawCommon (NBG_PaymentValidators.tc p)) := by rfl

theorem withdrawal_common (p : W) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.withdrawal_common (toRawWithdrawal p) =
    ok (toRawCommon (NBG_PaymentValidators.wc p)) := by rfl

theorem digest_canonical (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical d =
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical d := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem canonical_result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical d =
    ok (NBG_PaymentChecks.canonical d) := by
  rw [digest_canonical,NBG_PaymentChecks.canonical_result]

#print axioms transfer_common
#print axioms withdrawal_common
#print axioms digest_canonical
#print axioms canonical_result
end NED_PaymentCohorts
