import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_ParserR19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR08
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let r ← R1Z.PV_RJDec_ParserR19.program bytes
  invoke "core.result.Result.map_err" (fun ops =>
    letI : ProverRwFull.ExternalFuns := ops
    core.result.Result.map_err (BuiltinFnOnce pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) r (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransitionConstructor))

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1 bytes := by
  unfold program pool_v1.pair_forest_terminal.decode_lane_transition_boxed_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact R1Z.PV_RJDec_ParserR19.source ops bytes
  · intro r
    exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_ParserR08
