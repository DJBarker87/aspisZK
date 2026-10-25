import S6NativePaymentRoundtripV1
import S6NativeLateCodecV1
import S6NativeForestValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestDecodeHelpers
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

@[step] theorem size_spec : POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ⦃ result => result.val=1880 ⦄ := by
  unfold POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  step*

@[step] theorem payment_offset_spec : PAYMENT_STATEMENT_OFFSET ⦃ result => result.val=1664 ⦄ := by
  unfold PAYMENT_STATEMENT_OFFSET LATE_STATEMENT_OFFSET
  step*

@[step] theorem kind_spec (byte : U8) : transition_kind byte
    ⦃ result => ∀ kind, result=core.result.Result.Ok kind → (read_discriminant kind : U8)=byte ⦄ := by
  unfold transition_kind
  step*
  all_goals (intro kind accepted; cases accepted)
  all_goals first
    | (change 1#u8=_; scalar_tac)
    | (change 2#u8=_; scalar_tac)

@[step] theorem late_box_spec (bytes : Slice U8) : decode_lane_transition_boxed_v1 bytes
    ⦃ result => ∀ value, result=core.result.Result.Ok value →
      pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok value) ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeLateDecodeTotal.decode_total bytes
  apply exists_imp_spec
  cases result with
  | Ok value =>
    refine ⟨core.result.Result.Ok value,?_,?_⟩
    · simp [decode_lane_transition_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce]
    · intro v eq; cases eq; exact run
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairForestTerminalFormatErrorV1.LaneTransition error),?_,?_⟩
    · simp [decode_lane_transition_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
        PoolV1PairForestTerminalFormatErrorV1.LaneTransitionConstructor]
    · intro v eq; cases eq

@[step] theorem map_0_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err decode_terminal_common_boxed_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

#print axioms map_0_spec

@[step] theorem map_1_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err decode_terminal_common_boxed_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

#print axioms map_1_spec

@[step] theorem map_2_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err decode_terminal_common_boxed_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

#print axioms map_2_spec

@[step] theorem map_3_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err decode_terminal_common_boxed_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

#print axioms map_3_spec

@[step] theorem map_4_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err decode_terminal_common_boxed_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

#print axioms map_4_spec

@[step] theorem map_5_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err decode_terminal_common_boxed_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

#print axioms map_5_spec

#print axioms size_spec
#print axioms payment_offset_spec
#print axioms kind_spec
#print axioms late_box_spec
end AspisS6NativeForestDecodeHelpers
