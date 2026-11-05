import Lean
import AspisR1TerminalDecoder.Funs

set_option autoImplicit false
noncomputable section
namespace NGF_NEX_LaneOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
def run (late : Slice U8 → Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1)) (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let r ← late bytes
  AspisR1TerminalDecoder.core.result.Result.map_err (BuiltinFnOnce pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) r (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransitionConstructor)

/-- Model continuation substitution only. Native certificates and reached
child domains are separate checked obligations; no native root is assumed. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1 bytes,state,[]) := by rfl
#print axioms result_state_effects
end NGF_NEX_LaneOracle

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
