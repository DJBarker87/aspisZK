import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_ParserR12
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR07
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) := do
  let r ← R1Z.PV_RJDec_ParserR12.program bytes
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.map_err (BuiltinFnOnce pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) r (pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.SnapshotConstructor))
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    pure (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1 bytes := by
  unfold program pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact R1Z.PV_RJDec_ParserR12.source ops bytes
  · intro r
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          rfl
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_ParserR07
