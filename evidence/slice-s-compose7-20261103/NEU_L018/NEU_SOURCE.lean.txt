import NEU_CommonProjections
import NEU_BoxDecodeModel
import NED_PaymentCohorts
set_option autoImplicit false
noncomputable section
namespace NEU_DecoderProjections
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Common := PoolV1PairForestTerminalCommonV1
abbrev Transfer := NED_PaymentCohorts.T
abbrev Withdrawal := NED_PaymentCohorts.W

theorem common_ext (c d : Common)
    (point : ∀ slot i j k,
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon c) slot i j k =
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon d) slot i j k) : c=d := by
  have same := NEU_CommonProjections.common_ext _ _ point
  have back := congrArg NED_ReconstructCarriers.fromRawCommon same
  simpa only [NED_ReconstructCarriers.common_roundtrip] using back

theorem transfer_ext (c d : Common) (p q : Transfer)
    (commonPoint : ∀ slot i j k,
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon c) slot i j k =
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon d) slot i j k)
    (publicPoint : ∀ slot i j,
      NEU_PublicProjections.transfer (NED_PaymentCohorts.toRawTransfer p) slot i j =
      NEU_PublicProjections.transfer (NED_PaymentCohorts.toRawTransfer q) slot i j) :
    (PoolV1PairForestTerminalStatementV1.PrivateTransfer c p) = .PrivateTransfer d q := by
  have hc := common_ext c d commonPoint
  have hp := NEU_PublicProjections.transfer_ext _ _ publicPoint
  have raw : NED_ReconstructCarriers.toRaw (.PrivateTransfer c p) =
      NED_ReconstructCarriers.toRaw (.PrivateTransfer d q) := by
    change AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer
      (NED_ReconstructCarriers.toRawCommon c) (NED_PaymentCohorts.toRawTransfer p) =
      .PrivateTransfer (NED_ReconstructCarriers.toRawCommon d) (NED_PaymentCohorts.toRawTransfer q)
    rw [hc,hp]
  have back := congrArg NED_ReconstructCarriers.fromRaw raw
  simpa only [NED_ReconstructCarriers.statement_roundtrip] using back

theorem withdrawal_ext (c d : Common) (p q : Withdrawal)
    (commonPoint : ∀ slot i j k,
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon c) slot i j k =
      NEU_CommonProjections.value (NED_ReconstructCarriers.toRawCommon d) slot i j k)
    (publicPoint : ∀ slot i j,
      NEU_PublicProjections.withdrawal (NED_PaymentCohorts.toRawWithdrawal p) slot i j =
      NEU_PublicProjections.withdrawal (NED_PaymentCohorts.toRawWithdrawal q) slot i j) :
    (PoolV1PairForestTerminalStatementV1.Withdrawal c p) = .Withdrawal d q := by
  have hc := common_ext c d commonPoint
  have hp := NEU_PublicProjections.withdrawal_ext _ _ publicPoint
  have raw : NED_ReconstructCarriers.toRaw (.Withdrawal c p) =
      NED_ReconstructCarriers.toRaw (.Withdrawal d q) := by
    change AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal
      (NED_ReconstructCarriers.toRawCommon c) (NED_PaymentCohorts.toRawWithdrawal p) =
      .Withdrawal (NED_ReconstructCarriers.toRawCommon d) (NED_PaymentCohorts.toRawWithdrawal q)
    rw [hc,hp]
  have back := congrArg NED_ReconstructCarriers.fromRaw raw
  simpa only [NED_ReconstructCarriers.statement_roundtrip] using back

theorem payment_packet (b : Array U8 216#usize) : b.to_slice.val.length=216 := b.property

#print axioms common_ext
#print axioms transfer_ext
#print axioms withdrawal_ext
#print axioms payment_packet
end NEU_DecoderProjections
