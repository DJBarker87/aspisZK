import RPz7_S6NativeSnapshotDecoderFactoredV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecodeHelpers
open AspisR1TerminalDecoder

@[step] theorem format_graph : pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
    ⦃ result => pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING=ok result ⦄ := by
  obtain ⟨result,run,_⟩ := spec_imp_exists AspisS6NativeSnapshotEncodeTotal.format_spec
  apply exists_imp_spec
  exact ⟨result,run,run⟩

@[step] theorem map_0_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_1_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_2_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_3_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_4_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_5_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_6_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_7_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_8_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_9_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_10_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_11_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_12_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_13_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_14_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_15_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_16_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_17_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_18_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_19_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]

@[step] theorem map_20_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1,pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1.call_once]


#print axioms format_graph
#print axioms map_0_spec
#print axioms map_20_spec
end AspisS6NativeSnapshotDecodeHelpers
