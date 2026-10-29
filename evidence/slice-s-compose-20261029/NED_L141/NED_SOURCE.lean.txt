import NED_StatementCarrierFields
import NED_OutputLaneCohort
set_option autoImplicit false
noncomputable section
namespace NED_RawValidatorTail
open Aeneas Aeneas.Std Result NBN_StatementResult NED_ErrorCarriers
attribute [local instance] Classical.propDecidable
abbrev RE := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def run (s : Statement) : Result (core.result.Result Unit RE) := do
  let lane ← AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 (parts s).2.2.2.2.1
  match lane with
  | .Err e => ok (.Err (.Account e))
  | .Ok l =>
    if l ≠ (common s).output_lane then ok (.Err .OutputLaneMismatch)
    else do
      let (r,_) ← AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
        (NED_LateCarriers.toRawLate (common s).lane_transition) NBN_LateResult.zero
      match r with
      | .Err e => ok (.Err (.LaneTransition e))
      | .Ok _ => ok (.Ok ())

theorem result (s : Statement) : run s = ok
    (NED_LateValidatorCohorts.mapResult toRawPoolV1PairForestTerminalFormatErrorV1 (NBN_BindingChecks.tail s)) := by
  unfold run NBN_BindingChecks.tail
  rw [NED_OutputLaneCohort.result]
  cases lane : NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => rfl
  | Ok l =>
    simp only [NED_OutputLaneCohort.mapAccount,bind_tc_ok]
    by_cases mismatch : l = (common s).output_lane
    · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
      rw [NED_LateEncodingCohort.result,NBN_LateResult.source]
      have len : NBN_LateResult.zero.length = 1520 := by
        simp only [NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      rw [if_neg (not_not.mpr len)]
      unfold lateStatus
      by_cases index : U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 =
          some (common s).lane_transition.candidate_afterstate.next_pair_index
      · simp only [if_neg (not_not.mpr index),NED_LiveEncodingCohort.mapStateOuter,bind_tc_ok,Aeneas.Std.uncurry]
        cases NBN_LateTail.status (common s).lane_transition <;> rfl
      · simp [index,NED_LiveEncodingCohort.mapStateOuter,NED_LateValidatorCohorts.mapResult,
          toRawPoolV1PairForestTerminalFormatErrorV1,toRawPoolV1PairLatePublicStatementErrorV1]
    · simp [mismatch,NED_LateValidatorCohorts.mapResult,toRawPoolV1PairForestTerminalFormatErrorV1]

#print axioms result
end NED_RawValidatorTail
