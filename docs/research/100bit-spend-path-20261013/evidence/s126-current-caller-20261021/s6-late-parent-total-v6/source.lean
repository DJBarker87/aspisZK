import S6LateParentSourceV1
import S6SnapshotLoopParentTotalV1
import S6AfterstateLoopParentTotalV1
import S6SliceFrameLengthV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6LateParent.Total
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_tree_profile

@[step] theorem size_spec : POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    ⦃ result => result.val=1520 ⦄ := by
  unfold POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*

@[step] theorem option_u64_spec (a b : Option U64) :
    AspisS6StdOptionMethods.option_eq core.cmp.PartialEqU64 a b ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases a <;> cases b <;>
    simp [AspisS6StdOptionMethods.option_eq,
      AspisS6StdOptionMethods.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.cmp.PartialEqU64, liftFun2]

@[step] theorem option_ne_spec (a b : Option U64) :
    core.cmp.PartialEq.ne.default
      (AspisS6StdOptionMethods.option_eq core.cmp.PartialEqU64) a b
      ⦃ _ => True ⦄ := by
  unfold core.cmp.PartialEq.ne.default
  step*

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

/-- TOTAL enclosing lane-transition encoder reference, including every error
branch and mutable output frame. Concrete snapshot/afterstate implementations
are installed; there are no child-success premises. -/
@[step] theorem encode_spec (statement : PoolV1PairLatePublicStatementV1)
    (output : Slice U8) :
    encode statement output ⦃ result => result.2.length=output.length ⦄ := by
  unfold encode encode_pool_v1_pair_late_public_statement_v1
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
    core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEq.ne.trait_default
    core.result.Result.map_err
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1.call_once
    encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1.call_once
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)

theorem encode_total (statement : PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    ∃ result, encode statement output=ok result ∧ result.2.length=output.length := by
  exact spec_imp_exists (encode_spec statement output)

#print axioms size_spec
#print axioms option_u64_spec
#print axioms encode_total
end AspisS6LateParent.Total
