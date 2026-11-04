import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
noncomputable section
namespace NEX_SnapshotBoxOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
def run (snapshot : Slice U8 → Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1)) (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) := do
  let r ← snapshot bytes
  let r1 ← core.result.Result.map_err (BuiltinFnOnce pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) r (pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.SnapshotConstructor)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual

/-- Model continuation substitution only. Native certificates and reached
child domains are separate checked obligations; no native root is assumed. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1 bytes,state,[]) := by rfl
#print axioms result_state_effects
end NEX_SnapshotBoxOracle
