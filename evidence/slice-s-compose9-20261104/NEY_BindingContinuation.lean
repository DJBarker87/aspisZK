import JHb_S2K_ResultBinding
import NBN_LateFactor
set_option autoImplicit false
noncomputable section
namespace NEY_BindingContinuation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open AspisR1.S2K
abbrev Statement := StatementAdmission.Statement
abbrev Output := ResultAdmission.Output
abbrev Error := PoolV1PairForestTerminalFormatErrorV1

def run (sv : Statement → Result (core.result.Result Unit Error))
    (rv : Output → Result (core.result.Result Unit Error)) (s : Statement) :
    Result (core.result.Result Unit Error) := do
  let first ← sv s
  match first with
  | .Err e => ok (.Err e)
  | .Ok () => rv (ResultAdmission.value s)

/-- Total continuation on the caller-derived result. Neither validator success
is a premise; the complete first and second Results are preserved in order. -/
theorem result (s : Statement) :
    run validate_pool_v1_pair_forest_terminal_statement_v1 validate_result s =
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (ResultAdmission.value s) := by
  unfold run validate_pool_v1_pair_forest_terminal_result_against_statement_v1
  apply NBN_LateFactor.bind_ext
  intro first
  cases first with
  | Err e => rfl
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply NBN_LateFactor.bind_ext
    intro second
    cases second with
    | Err e => rfl
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      cases s <;> simp [ResultAdmission.value,ResultAdmission.kind,
        StatementAdmission.common,StatementChecks.nullifier,
        PoolV1PairForestTerminalStatementV1.common,
        PoolV1PairForestTerminalStatementV1.transition_kind,
        PoolV1PairForestTerminalStatementV1.nullifier,
        core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
        pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind.eq,
        ResultBinding.byte_array_ne_self,ResultBinding.digest_ne_self,ResultBinding.afterstate_self]

#print axioms result
end NEY_BindingContinuation
