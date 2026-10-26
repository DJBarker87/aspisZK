import S6SourcePaymentCommonDecodeV1
import S6StdByteSliceEqualityV1
import RPz7_S6NativeAfterstateValidatorTotalV1
import RPz7_S6NativeDigestEncodeSourceEqV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeAfterstateDecodeHelpers
open AspisR1TerminalDecoder
open pool_v1.pair_terminal

@[step] theorem size_spec : POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    ⦃ result => result.val=688 ⦄ := by
  unfold POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*

@[step] theorem exact_spec (N : Usize) (bytes : Slice U8) :
    «exact» N bytes ⦃ result => match result with
      | core.result.Result.Ok array => array.val=bytes.val ∧ bytes.length=N.val
      | core.result.Result.Err error => bytes.length≠N.val ∧ error=PoolV1PairVerifierTransportErrorV1.WrongLength ⦄ := by
  unfold «exact»
  step*
  cases r with
  | Ok array =>
    simp_all [core.result.Result.map_err,
    pool_v1.pair_terminal.exact.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairVerifierTransportErrorV1,
    pool_v1.pair_terminal.exact.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairVerifierTransportErrorV1.call_once]
    rw [←r_post]
    exact array.property
  | Err error =>
    simp_all [core.result.Result.map_err,
    pool_v1.pair_terminal.exact.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairVerifierTransportErrorV1,
    pool_v1.pair_terminal.exact.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_0_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_1_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_2_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_3_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_4_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_5_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_6_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_7_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_8_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_9_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_10_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_11_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_12_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_13_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_14_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_15_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_16_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_17_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_18_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_19_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

@[step] theorem map_20_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1,pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1.call_once]

#print axioms size_spec
#print axioms exact_spec

end AspisS6NativeAfterstateDecodeHelpers
