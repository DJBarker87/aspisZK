import NED_StatementCarrierFields
import NED_OutputLaneCohort
set_option autoImplicit false
noncomputable section
namespace NED_RawValidatorCohort
open Aeneas Aeneas.Std Result NED_ReconstructCarriers NED_ErrorCarriers
open AspisR1AdapterReconstruct
attribute [local instance] Classical.propDecidable

theorem result (s : Terminal) :
    aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 (toRaw s) =
    ok (NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 (NED_ValidatorStatus.status s)) := by
  unfold aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  rw [NED_ReconstructCarriers.common_argument]
  simp only [bind_tc_ok,NBH_ArrayEq.source,NED_StatementCarrierFields.master,
    NED_StatementCarrierFields.checkpoint,NED_StatementCarrierFields.selected_lane,NED_StatementCarrierFields.lane,
    NED_StatementCarrierFields.sequence,NED_LateCarrierFields.common_late,NED_LateCarrierFields.common_anchor,
    NED_LateCarrierFields.live,NED_StatementCarrierFields.pool,NED_StatementCarrierFields.deployment,
    NED_ReconstructCarriers.parts_argument,NBN_ArrayNe.bytes,NED_RawWordArrayEq.ne,
    NED_OutputLaneCohort.result,NED_LateEncodingCohort.result]
  have cast : core.convert.num.FromUsizeU8.from (NBN_StatementResult.common s).output_lane =
      Usize.ofNatCore (NBN_StatementResult.common s).output_lane.val (by scalar_tac) := by scalar_tac
  simp only [cast,lift,bind_tc_ok,
    aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT,
    Bool.or_eq_true,decide_eq_true_eq]
  unfold NED_ValidatorStatus.status
  dsimp (config := {zeta := true,zetaHave := true}) only
  by_cases zero : (NBN_StatementResult.common s).master_account = NBN_StatementResult.zero ∨
      (NBN_StatementResult.common s).checkpoint_account = NBN_StatementResult.zero ∨
      (NBN_StatementResult.common s).selected_lane_account = NBN_StatementResult.zero
  · simp only [NBN_StatementResult.zero,NBK_StatementPrefix.zero] at zero
    rcases zero with hm | hc | hs
    all_goals simp_all [NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1]
  · simp only [if_neg zero]
    simp only [NBN_StatementResult.zero,NBK_StatementPrefix.zero,not_or] at zero
    simp only [zero.1,zero.2.1,zero.2.2,if_false]
    by_cases lane : 8 ≤ (NBN_StatementResult.common s).output_lane.val
    · have large : (Usize.ofNatCore (NBN_StatementResult.common s).output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
      simp [lane,large,NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1]
    · have small : ¬ (Usize.ofNatCore (NBN_StatementResult.common s).output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
      simp only [if_neg lane,if_neg small]
      cases s with
      | PrivateTransfer c p =>
        simp only [NED_StatementCarrierFields.transfer,NED_ValidatorStatus.payment]
        rw [NED_TransferEncodingCohort.result]
        cases pay : NBP_PaymentModel.transfer_encoded p with
        | Err e => simp [pay,NED_CommonValidation.mapPayment,NED_LateValidatorCohorts.mapResult,
            toRawPoolV1PairForestTerminalFormatErrorV1,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
        | Ok bytes =>
          simp only [pay,NED_CommonValidation.mapPayment,bind_tc_ok,core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch]
          simp only [NBN_StatementResult.suffix,NBN_StatementResult.lateStatus,
            NED_OutputLaneCohort.mapAccount,NED_LiveEncodingCohort.mapStateOuter,
            NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1,
            Array.to_slice_mut,lift,bind_tc_ok,Aeneas.Std.uncurry,NBN_LateResult.source,
            Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
          repeat' first | rfl | (split <;> try simp_all only [bind_tc_ok,decide_eq_true_eq,bne_iff_ne])
      | Withdrawal c p =>
        simp only [NED_StatementCarrierFields.withdrawal,NED_ValidatorStatus.payment]
        rw [NED_WithdrawalEncodingCohort.result]
        cases pay : NBP_PaymentModel.withdrawal_encoded p with
        | Err e => simp [pay,NED_CommonValidation.mapPayment,NED_LateValidatorCohorts.mapResult,
            toRawPoolV1PairForestTerminalFormatErrorV1,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
        | Ok bytes =>
          simp only [pay,NED_CommonValidation.mapPayment,bind_tc_ok,core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch]
          simp only [NBN_StatementResult.suffix,NBN_StatementResult.lateStatus,
            NED_OutputLaneCohort.mapAccount,NED_LiveEncodingCohort.mapStateOuter,
            NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1,
            Array.to_slice_mut,lift,bind_tc_ok,Aeneas.Std.uncurry,NBN_LateResult.source,
            Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
          repeat' first | rfl | (split <;> try simp_all only [bind_tc_ok,decide_eq_true_eq,bne_iff_ne])

#print axioms result
end NED_RawValidatorCohort
