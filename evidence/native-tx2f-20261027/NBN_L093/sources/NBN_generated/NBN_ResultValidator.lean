import S2K_ResultNativeSource
import NBN_U05
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_ResultValidator
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open pool_v1.pair_forest_terminal
attribute [local instance] Classical.propDecidable
abbrev Record := PoolV1PairForestTerminalResultV1

def status (r : Record) : core.result.Result Unit NBN_StatementResult.Error :=
  if r.master_account = zero ∨ r.selected_lane_account = zero then .Err .NonZeroBinding
  else match NBN_OutputLane.result r.nullifier with
    | .Err e => .Err (.Account e)
    | .Ok lane => if r.output_lane ≠ lane then .Err .OutputLaneMismatch
      else match NBH_Validators.afterResult r.verified_afterstate with
        | .Err e => .Err (.Afterstate e)
        | .Ok _ => .Ok ()

theorem source (r : Record) : validate_result r = ok (status r) := by
  unfold validate_result
  simp only [NBH_ArrayEq.source,bind_tc_ok,NBN_OutputLane.source,NBK_AfterstateResult.source]
  unfold status
  repeat' first
    | rfl
    | (split <;> try simp_all only [decide_eq_true_eq,bne_iff_ne,bind_tc_ok,
        core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch])

#print axioms source
end NBN_ResultValidator
