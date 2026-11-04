import Lean
import NGE_NBN_ResultValidator
import NFY_Part030

set_option autoImplicit false
noncomputable section
namespace NGE_NBN_ResultDependency
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NFY_NBN_StatementResult NGE_NBN_ResultValidator
attribute [local instance] Classical.propDecidable

def run (enc : NFY_NBN_EncoderSummary.Encode) (r : Record) : Result (core.result.Result Unit NFY_NBN_StatementResult.Error) :=
  if r.master_account = zero ∨ r.selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else do
    let lane ← NFY_NBN_FirstByteDependency.lane enc r.nullifier
    match lane with
    | .Err e => ok (.Err (.Account e))
    | .Ok l =>
      if r.output_lane ≠ l then ok (.Err .OutputLaneMismatch)
      else do
        let a ← NFY_NBN_EncoderSummary.after enc r.verified_afterstate
        match a with
        | .Err e => ok (.Err (.Afterstate e))
        | .Ok _ => ok (.Ok ())

theorem source (enc : NFY_NBN_EncoderSummary.Encode)
    (NBN_Dep_DigestEncodeCanonical : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc) (r : Record) :
    run enc r = pool_v1.pair_forest_terminal.validate_result r := by
  rw [NGE_NBN_ResultValidator.source]
  unfold run status
  simp only [NFY_NBN_FirstByteDependency.lane_source enc NBN_Dep_DigestEncodeCanonical,NFY_NBN_OutputLane.source,
    NFY_NBN_EncoderSummary.after_source enc NBN_Dep_DigestEncodeCanonical,NFY_NBK_AfterstateResult.source]
  by_cases h : r.master_account = zero ∨ r.selected_lane_account = zero
  · simp only [h,if_true]
  · simp only [h,if_false,bind_tc_ok]
    cases NFY_NBN_OutputLane.result r.nullifier with
    | Err e => rfl
    | Ok lane =>
      by_cases mismatch : r.output_lane = lane
      · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
        cases NFY_NBH_Validators.afterResult r.verified_afterstate <;> rfl
      · simp only [mismatch,ne_eq,not_false_eq_true,if_true]

#print axioms source
end NGE_NBN_ResultDependency

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
