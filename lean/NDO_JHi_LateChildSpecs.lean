import NDO_JHi_SnapshotAccepted
import NDO_JHi_AfterstateAccepted
import S6NativeSliceFrameLengthV1
set_option autoImplicit false
namespace AspisR1.JHi_LateChildSpecs
open Aeneas Aeneas.Std Result WP
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1.pair_tree_profile

@[step] theorem snapshot_spec (output : Slice U8) (size : output.length=800) :
    encode_pool_v1_pair_live_snapshot_v1 JHg_RawCommon.common.lane_transition.live_snapshot output
      ⦃ result => result.1=core.result.Result.Ok () ∧
        encode_pool_v1_pair_live_snapshot_v1 JHg_RawCommon.common.lane_transition.live_snapshot output=ok result ∧
        result.2.length=800 ⦄ := by
  obtain ⟨updated,run,len⟩:=JHi_SnapshotAccepted.source output size
  rw [run,WP.spec_ok]
  exact ⟨rfl,rfl,len⟩

@[step] theorem afterstate_spec :
    aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
      JHg_RawCommon.common.lane_transition.candidate_afterstate
      ⦃ result => ∃ encoded : Array U8 688#usize, result=core.result.Result.Ok encoded ∧
        aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
          JHg_RawCommon.common.lane_transition.candidate_afterstate=ok (core.result.Result.Ok encoded) ⦄ := by
  obtain ⟨encoded,run⟩:=JHi_AfterstateAccepted.source
  rw [run,WP.spec_ok]
  exact ⟨encoded,rfl,rfl⟩

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

@[step] theorem map_afterstate {T : Type} (r : core.result.Result T aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
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
end AspisR1.JHi_LateChildSpecs
