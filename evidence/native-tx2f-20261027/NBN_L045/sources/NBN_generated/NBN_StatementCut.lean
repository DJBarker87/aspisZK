import NBN_BindingChecks
set_option autoImplicit false
noncomputable section
namespace NBN_StatementCut
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev PE := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev AE := pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev LE := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
abbrev E := NBN_StatementResult.Error

def tail (s : Statement) (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) :
    core.result.Result Unit E :=
  match lane with
  | .Err e => .Err (.Account e)
  | .Ok l => if l ≠ (common s).output_lane then .Err .OutputLaneMismatch
    else match late with
      | .Err e => .Err (.LaneTransition e)
      | .Ok _ => .Ok ()

/-- Exact native K003 control cut. Child values are arbitrary, not successful. -/
def run (s : Statement) (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) : Result (core.result.Result Unit E) :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else if 8 ≤ (common s).output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let r ← pay
    match r with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => ok (NBN_BindingChecks.chain (common s) (parts s) (tail s lane late))

theorem source (s : Statement) :
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s =
      run s (payment s) (NBN_OutputLane.result (parts s).2.2.2.2.1)
        (lateStatus (common s).lane_transition) := by
  rw [NBN_StatementResult.source]
  cases s <;> rfl

/-- Substitution uses only exact lower Results on the SAME input/variant. -/
theorem lower_substitution (s : Statement)
    (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE)
    (payment_exact : pay = payment s)
    (lane_exact : lane = NBN_OutputLane.result (parts s).2.2.2.2.1)
    (late_exact : late = lateStatus (common s).lane_transition) :
    run s pay lane late =
      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [payment_exact,lane_exact,late_exact,source]

#print axioms source
#print axioms lower_substitution
end NBN_StatementCut
