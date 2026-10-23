import S6SnapshotLoopParentSourceV1
import S6SnapshotHelperTotalV1
import S6SourceSnapshotValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SnapshotLoopParent.Total
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_tree_profile

theorem frontier_eq (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8) :
    frontier_loop_reference snapshot output =
      AspisS6SnapshotHelper.frontier_loop snapshot output := by rfl

@[step] theorem frontier_spec (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8)
    (hn : output.length=800) :
    frontier_loop_reference snapshot output ⦃ result => result.length=800 ⦄ := by
  rw [frontier_eq]
  obtain ⟨result,h,hlen⟩ := AspisS6SnapshotHelper.Total.frontier_total snapshot output hn
  rw [h,WP.spec_ok]
  exact hlen

@[step] theorem validator_spec (snapshot : PoolV1PairLiveSnapshotV1) :
    AspisS6SourceCodec.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 snapshot
      ⦃ _ => True ⦄ := by
  obtain ⟨result,h⟩ := AspisS6SourceCodec.SnapshotTotal.snapshot_total snapshot
  rw [h,WP.spec_ok]
  trivial

@[step] theorem format_spec : POOL_V1_PAIR_TREE_FORMAT_BINDING ⦃ _ => True ⦄ := by
  unfold POOL_V1_PAIR_TREE_FORMAT_BINDING POOL_V1_PAIR_TREE_DEPTH
    POOL_V1_PAIR_NOTE_DEPTH POOL_V1_PAIR_SECOND_SENTINEL_LANE
  step*

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

/-- TOTAL enclosing snapshot encoder reference for every mutable output slice,
including wrong lengths and inner errors; the argument frame retains its length. -/
@[step] theorem encode_spec (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8) :
    encode snapshot output ⦃ result => result.2.length=output.length ⦄ := by
  unfold encode encode_pool_v1_pair_live_snapshot_v1 POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

theorem encode_total (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8) :
    ∃ result, encode snapshot output=ok result ∧ result.2.length=output.length := by
  exact spec_imp_exists (encode_spec snapshot output)

#print axioms frontier_eq
#print axioms frontier_spec
#print axioms format_spec
#print axioms encode_total
end AspisS6SnapshotLoopParent.Total
