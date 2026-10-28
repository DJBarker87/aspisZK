import NBN_LateTail
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result
namespace NBN_LateFactor
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def raw (statement : PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    Result (core.result.Result Unit PoolV1PairLatePublicStatementErrorV1 × Slice U8) := do
      let i7 ← 32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output { start := 32#usize, «end» := i7 }
      let (r, s16) ← pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 statement.live_snapshot s15
      let r1 ← core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 statement.candidate_afterstate
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


theorem raw_eq (s : PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    raw s output = NBN_LateTail.run s output := by
  unfold raw NBN_LateTail.run
  simp only [core.result.Result.map_err,
    encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1.call_once,
    encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,Bind.bind,Aeneas.Std.bind]
  repeat' first | rfl | split

theorem factor (s : PoolV1PairLatePublicStatementV1) (output : Slice U8)
    (size : output.length = 1520)
    (index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
      some s.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 s output =
      (do let filled ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
          NBN_LatePrepare.run filled (NBN_LateTail.run s)) := by
  have len : Slice.len output = 1520#usize := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.JFs_LateConstants.size,bind_tc_ok,len,bne_self_eq_false,if_false,
    lift,NBK_LatePreflight.option_ne,index,ne_eq,not_true_eq_false,decide_false]
  unfold NBN_LatePrepare.run
  simp only [← raw_eq]
  rfl

#print axioms raw_eq
#print axioms factor
end NBN_LateFactor
