import Lean
import NFY_Part033
import NFY_Part029

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NGE_NBN_ResultValidator
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
open pool_v1.pair_forest_terminal
attribute [local instance] Classical.propDecidable
abbrev Record := PoolV1PairForestTerminalResultV1

def status (r : Record) : core.result.Result Unit NFY_NBN_StatementResult.Error :=
  if r.master_account = zero ∨ r.selected_lane_account = zero then .Err .NonZeroBinding
  else match NFY_NBN_OutputLane.result r.nullifier with
    | .Err e => .Err (.Account e)
    | .Ok lane => if r.output_lane ≠ lane then .Err .OutputLaneMismatch
      else match NFY_NBH_Validators.afterResult r.verified_afterstate with
        | .Err e => .Err (.Afterstate e)
        | .Ok _ => .Ok ()

theorem source (r : Record) : validate_result r = ok (status r) := by
  unfold validate_result
  simp only [NBH_ArrayEq.source,bind_tc_ok,NFY_NBN_OutputLane.source,NFY_NBK_AfterstateResult.source]
  unfold status
  repeat' first
    | rfl
    | (split <;> try simp_all only [decide_eq_true_eq,bne_iff_ne,bind_tc_ok,
        AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch])

  all_goals simp_all [
    validate_result.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once,
    validate_result.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]

#print axioms source
end NGE_NBN_ResultValidator

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
