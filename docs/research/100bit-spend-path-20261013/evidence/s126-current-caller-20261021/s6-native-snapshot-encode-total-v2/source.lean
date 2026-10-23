import S6NativeSnapshotLoopV1
import S6NativeSnapshotValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotEncodeTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisR1.S2K

@[step] theorem digest_spec (digest : Array U32 8#usize) :
    atomic_statement.encode_digest_canonical digest
      ⦃ output => output.val=AspisS6SourceCodec.DigestContents.chunks digest ⦄ := by
  rw [AspisS6NativeDigestEncodeSourceEq.encode_eq]
  exact AspisS6SourceCodec.DigestContents.encode_contents digest

theorem fold_length (nodes : List AspisS6NativeSnapshotLoopStep.Digest) (level : Nat) (output : Slice U8) :
    (AspisS6NativeSnapshotLoop.fold nodes level output).length=output.length := by
  induction nodes generalizing level output with
  | nil => rfl
  | cons node tail ih =>
    simp only [AspisS6NativeSnapshotLoop.fold]
    rw [ih,AspisS6NativeSnapshotStore.write_length]

@[step] theorem frontier_spec (rows : AspisS6NativeSnapshotLoop.Rows)
    (count : Usize) (output : Slice U8) (bound : count.val≤20) (size : output.length=800) :
    encode_pool_v1_pair_live_snapshot_v1_loop (Iterator.cursor rows count) output
      ⦃ result => result.length=output.length ⦄ := by
  rw [AspisS6NativeSnapshotLoop.loop_exact rows count bound output size,WP.spec_ok]
  exact fold_length _ _ output

@[step] theorem format_spec : POOL_V1_PAIR_TREE_FORMAT_BINDING ⦃ _ => True ⦄ := by
  unfold POOL_V1_PAIR_TREE_FORMAT_BINDING POOL_V1_PAIR_NOTE_DEPTH
    POOL_V1_PAIR_TREE_DEPTH POOL_V1_PAIR_SECOND_SENTINEL_LANE
    pool_v1.format.POOL_V1_TREE_DEPTH
  step*

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

/-- TOTAL actual original native mutable encoder. All native record fields,
output slices, error branches and the returned output frame are retained. -/
@[step] theorem encode_spec (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8) :
    encode_pool_v1_pair_live_snapshot_v1 snapshot output
      ⦃ result => result.2.length=output.length ⦄ := by
  unfold encode_pool_v1_pair_live_snapshot_v1 POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.slice.Slice.iter core.iter.traits.iterator.Iterator.enumerate.trait_default
    core.iter.traits.iterator.Iterator.enumerate.default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> scalar_tac)

theorem encode_total (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8) :
    ∃ result, encode_pool_v1_pair_live_snapshot_v1 snapshot output=ok result ∧
      result.2.length=output.length := by
  exact spec_imp_exists (encode_spec snapshot output)

#print axioms fold_length
#print axioms frontier_spec
#print axioms format_spec
#print axioms encode_total
end AspisS6NativeSnapshotEncodeTotal
