import NBN_ResultValidator
import NBN_U04
set_option autoImplicit false
noncomputable section
namespace NBN_ResultDependency
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NBN_StatementResult NBN_ResultValidator
attribute [local instance] Classical.propDecidable

def run (enc : NBN_EncoderSummary.Encode) (r : Record) : Result (core.result.Result Unit NBN_StatementResult.Error) :=
  if r.master_account = zero ∨ r.selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else do
    let lane ← NBN_FirstByteDependency.lane enc r.nullifier
    match lane with
    | .Err e => ok (.Err (.Account e))
    | .Ok l =>
      if r.output_lane ≠ l then ok (.Err .OutputLaneMismatch)
      else do
        let a ← NBN_EncoderSummary.after enc r.verified_afterstate
        match a with
        | .Err e => ok (.Err (.Afterstate e))
        | .Ok _ => ok (.Ok ())

theorem source (enc : NBN_EncoderSummary.Encode)
    (NBN_Dep_DigestEncodeCanonical : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc) (r : Record) :
    run enc r = pool_v1.pair_forest_terminal.validate_result r := by
  rw [NBN_ResultValidator.source]
  unfold run status
  simp only [NBN_FirstByteDependency.lane_source enc NBN_Dep_DigestEncodeCanonical,NBN_OutputLane.source,
    NBN_EncoderSummary.after_source enc NBN_Dep_DigestEncodeCanonical,NBK_AfterstateResult.source]
  by_cases h : r.master_account = zero ∨ r.selected_lane_account = zero
  · simp only [h,if_true]
  · simp only [h,if_false,bind_tc_ok]
    cases NBN_OutputLane.result r.nullifier with
    | Err e => rfl
    | Ok lane =>
      by_cases mismatch : r.output_lane = lane
      · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
        cases NBH_Validators.afterResult r.verified_afterstate <;> rfl
      · simp only [mismatch,ne_eq,not_false_eq_true,if_true]

#print axioms source
end NBN_ResultDependency
