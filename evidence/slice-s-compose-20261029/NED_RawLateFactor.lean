import NED_RawLateTail
import NBN_LateFactor
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result
namespace NED_RawLateFactor
open AspisR1AdapterReconstruct
open aspis_statement
open pool_v1.pair_tree_profile

def raw (statement : NED_LateCarriers.TLate) (output : Slice U8) :
    Result (core.result.Result Unit PoolV1PairLatePublicStatementErrorV1 × Slice U8) := do
      let i7 ← 32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output { start := 32#usize, «end» := i7 }
      let (r, s16) ← pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 (NED_LateCarriers.toRawSnapshot statement.live_snapshot) s15
      let r1 ← core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (NED_LateCarriers.toRawAfter statement.candidate_afterstate)
        let r3 ← core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 r2 ()
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val => let output9 := index_mut_back5 s16
                                                            let (s17, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) output9 { start := i7 }
                                                            let s18 ← lift (Array.to_slice val)
                                                            let s19 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s17 s18
                                                            let output10 := index_mut_back6 s19
                                                            ok (core.result.Result.Ok (), output10)
        | core.ops.control_flow.ControlFlow.Break residual => let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                              let output9 := index_mut_back5 s16
                                                              ok (r4, output9)
      | core.ops.control_flow.ControlFlow.Break residual => let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                            let output9 := index_mut_back5 s16
                                                            ok (r2, output9)


theorem raw_eq (s : NED_LateCarriers.TLate) (output : Slice U8) :
    raw s output = NED_RawLateTail.run s output := by
  unfold raw NED_RawLateTail.run
  apply NBN_LateFactor.bind_ext
  intro i7
  apply NBN_LateFactor.bind_ext
  intro window
  rcases window with ⟨input,back⟩
  apply NBN_LateFactor.bind_ext
  intro child
  rcases child with ⟨r,live⟩
  cases r with
  | Err e => rfl
  | Ok u =>
    cases u
    dsimp only [Aeneas.Std.uncurry]
    simp only [core.result.Result.map_err,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    apply NBN_LateFactor.bind_ext
    intro after
    cases after <;> rfl

#print axioms raw_eq
end NED_RawLateFactor
