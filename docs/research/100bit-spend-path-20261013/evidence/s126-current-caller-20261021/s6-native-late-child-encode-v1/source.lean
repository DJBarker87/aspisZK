import S6NativeSnapshotCodecV1
import S6NativeLateChildDecodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateChildEncode
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem snapshot_spec (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8)
    (size : output.length=800)
    (validated : validate_pool_v1_pair_live_snapshot_v1 snapshot=ok (core.result.Result.Ok ())) :
    encode_pool_v1_pair_live_snapshot_v1 snapshot output
      ⦃ result => result.1=core.result.Result.Ok () ∧
        encode_pool_v1_pair_live_snapshot_v1 snapshot output=ok result ∧ result.2.length=800 ⦄ := by
  obtain ⟨result,run,success⟩ := spec_imp_exists
    (AspisS6NativeSnapshotEncoderGraph.encode_success snapshot output size validated)
  have len := AspisS6NativeSnapshotEncodeTotal.encode_spec snapshot output
  rw [run,WP.spec_ok] at len
  apply exists_imp_spec
  exact ⟨result,run,success,run,len.trans size⟩

@[step] theorem afterstate_spec (afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (validated : pool_v1.pair_terminal.validate_verified_afterstate afterstate=ok (core.result.Result.Ok ())) :
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 afterstate
      ⦃ result => ∃ encoded : Array U8 688#usize, result=core.result.Result.Ok encoded ∧
        pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 afterstate=
          ok (core.result.Result.Ok encoded) ⦄ := by
  have run := AspisR1.S2K.AfterstateEncoding.encode_exact afterstate validated
  rw [run,WP.spec_ok]
  exact ⟨_,rfl,run⟩

@[step] theorem branch_graph {T : Type} (r : core.result.Result T PoolV1PairLatePublicStatementErrorV1) :
    core.result.Result.Insts.CoreOpsTry.branch r
      ⦃ cf => core.result.Result.Insts.CoreOpsTry.branch r=ok cf ⦄ := by
  apply exists_imp_spec
  cases r <;> exact ⟨_,rfl,rfl⟩

@[step] theorem map_snapshot {T : Type} (r : core.result.Result T PoolV1PairLiveSnapshotErrorV1) :
    core.result.Result.map_err encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      ⦃ result => ∀ value, r=core.result.Result.Ok value → result=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r with
  | Ok value =>
    refine ⟨core.result.Result.Ok value,?_,?_⟩
    · rfl
    · intro v eq; cases eq; rfl
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairLatePublicStatementErrorV1.Snapshot error),?_,?_⟩
    · simp [core.result.Result.map_err,encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1,encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1.call_once]
    · intro v eq; cases eq

@[step] theorem map_afterstate {T : Type} (r : core.result.Result T pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    core.result.Result.map_err encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      ⦃ result => ∀ value, r=core.result.Result.Ok value → result=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r with
  | Ok value =>
    refine ⟨core.result.Result.Ok value,?_,?_⟩
    · rfl
    · intro v eq; cases eq; rfl
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairLatePublicStatementErrorV1.Afterstate error),?_,?_⟩
    · simp [core.result.Result.map_err,encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1,encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1.call_once]
    · intro v eq; cases eq

#print axioms snapshot_spec
#print axioms afterstate_spec
#print axioms branch_graph
#print axioms map_snapshot
#print axioms map_afterstate
end AspisS6NativeLateChildEncode
