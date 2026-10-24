import S6NativeSnapshotEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateEncodeTotal
open AspisR1TerminalDecoder
open scoped AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem afterstate_spec (afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 afterstate ⦃ _ => True ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeAfterstateCodec.encode_total afterstate
  rw [run,WP.spec_ok]
  trivial

@[step] theorem size_spec : POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    ⦃ result => result.val=1520 ⦄ := by
  unfold POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*

@[step] theorem option_u64_spec (a b : Option U64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64 a b ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases a <;> cases b <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.cmp.PartialEqU64, liftFun2]

@[step] theorem option_ne_spec (a b : Option U64) :
    core.cmp.PartialEq.ne.default
      (core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64) a b
      ⦃ _ => True ⦄ := by
  unfold core.cmp.PartialEq.ne.default
  step*

@[step] theorem snapshot_map_spec {T : Type} (r : core.result.Result T PoolV1PairLiveSnapshotErrorV1) :
    core.result.Result.map_err encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err, encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1, encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1.call_once]

@[step] theorem afterstate_map_spec {T : Type} (r : core.result.Result T pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    core.result.Result.map_err encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err, encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1, encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1.call_once]

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

/-- TOTAL enclosing lane-transition encoder reference, including every error
branch and mutable output frame. Concrete snapshot/afterstate implementations
are installed; there are no child-success premises. -/
@[step] theorem encode_spec (statement : PoolV1PairLatePublicStatementV1)
    (output : Slice U8) :
    encode_pool_v1_pair_late_public_statement_v1 statement output ⦃ result => result.2.length=output.length ⦄ := by
  unfold encode_pool_v1_pair_late_public_statement_v1
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
    core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEq.ne.trait_default
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)

theorem encode_total (statement : PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    ∃ result, encode_pool_v1_pair_late_public_statement_v1 statement output=ok result ∧ result.2.length=output.length := by
  exact spec_imp_exists (encode_spec statement output)

#print axioms size_spec
#print axioms option_u64_spec
#print axioms encode_total
end AspisS6NativeLateEncodeTotal
