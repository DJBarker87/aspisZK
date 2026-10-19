import BatchedWeightsIndexedQueryLoopModelV18
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV7
open BatchedWeightsIndexedQueryLoopModelV2
abbrev Usize := BatchedWeightsIndexedQueryLoopModelV2.Usize
abbrev M := BatchedWeightsIndexedQueryLoopModelV2.M
abbrev Q := BatchedWeightsIndexedQueryLoopModelV2.Q
abbrev BW := BatchedWeightsIndexedQueryLoopModelV2.BW
abbrev Range := core.ops.range.Range Usize

def rangeCursorSegment (start count : Nat) : List Usize :=
  (List.range count).map fun i => rangeCursor (start + i)

theorem rangeCursorList_succ (k : Nat) :
    rangeCursorList (k + 1) = rangeCursorList k ++ [rangeCursor k] := by
  simp [rangeCursorList, List.range_succ, List.map_append]

theorem rangeCursorSegment_succ (k m : Nat) :
    rangeCursorSegment k (m + 1) = rangeCursor k :: rangeCursorSegment (k + 1) m := by
  induction m with
  | zero => simp [rangeCursorSegment]
  | succ m ih =>
      have hleft : rangeCursorSegment k (m + 1 + 1) =
          rangeCursorSegment k (m + 1) ++ [rangeCursor (k + (m + 1))] := by
        simp [rangeCursorSegment, List.range_succ, List.map_append]
      have hright : rangeCursorSegment (k + 1) (m + 1) =
          rangeCursorSegment (k + 1) m ++ [rangeCursor ((k + 1) + m)] := by
        simp [rangeCursorSegment, List.range_succ, List.map_append]
      rw [show Nat.succ m + 1 = m + 1 + 1 by omega, hleft, ih, hright]
      simp only [List.cons_append]
      congr 1
      congr 1
      have hnat : k + (m + 1) = (k + 1) + m := by omega
      rw [hnat]

theorem rangeCursorList_split (k m : Nat) :
    rangeCursorList (k + m) = rangeCursorList k ++ rangeCursorSegment k m := by
  unfold rangeCursorList rangeCursorSegment
  rw [List.range_add, List.map_append, List.map_map]
  simp only [Function.comp_def]

theorem array_slice_index {n : Usize} (a : Array M n) (i : Usize) :
    Array.index_usize a i = Slice.index_usize (Array.to_slice a) i := by rfl

theorem push_query_loop_body_success
    (power : Q) (basis : Array M 256#usize) (iter iterNext : Range)
    (acc accNext : BW) (index : Usize) (basisValue : M)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some index, iterNext))
    (hread : Array.index_usize basis index = .ok basisValue)
    (hpush : batched_weights.BatchedWeights.push acc index power basisValue = .ok accNext) :
    batched_weights.BatchedWeights.push_query_loop.body power basis iter acc =
      .ok (ControlFlow.cont (iterNext, accNext)) := by
  simp [batched_weights.BatchedWeights.push_query_loop.body, hnext, hread, hpush]

/-- Under the successful iterator/read/push facts, the generated body and the
V18 single-row model both return the same updated accumulator. -/
theorem push_query_loop_body_matches_single_row
    (power : Q) (basis : Array M 256#usize) (iter iterNext : Range)
    (acc accNext : BW) (index : Usize) (basisValue : M)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some index, iterNext))
    (hread : Array.index_usize basis index = .ok basisValue)
    (hpush : batched_weights.BatchedWeights.push acc index power basisValue = .ok accNext) :
    batched_weights.BatchedWeights.push_query_loop.body power basis iter acc =
      .ok (ControlFlow.cont (iterNext, accNext)) ∧
    readPushRows (Array.to_slice basis) (fun _ => power) [index] acc = .ok accNext := by
  constructor
  · exact push_query_loop_body_success power basis iter iterNext acc accNext index basisValue hnext hread hpush
  · have hsread : Slice.index_usize (Array.to_slice basis) index = .ok basisValue := by
      rw [← array_slice_index]
      exact hread
    simp [readPushRows, hsread, hpush]

#print axioms push_query_loop_body_matches_single_row
/-- One real `0..len` iterator step selects precisely V18's cursor and returns
the same one-row model result, assuming the actual row read and push succeed. -/
theorem indexed_loop_step_matches_model
    (power : Q) (basis : Array M 256#usize) (iter : Range)
    (acc accNext : BW) (basisValue : M)
    (hlt : iter.start.val < iter.end.val)
    (hread : Array.index_usize basis (rangeCursor iter.start.val) = .ok basisValue)
    (hpush : batched_weights.BatchedWeights.push acc (rangeCursor iter.start.val)
      power basisValue = .ok accNext) :
    ∃ iterNext : Range,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some (rangeCursor iter.start.val), iterNext) ∧
      iterNext.start = rangeCursor (iter.start.val + 1) ∧
      batched_weights.BatchedWeights.push_query_loop.body power basis iter acc =
        .ok (ControlFlow.cont (iterNext, accNext)) ∧
      readPushRows (Array.to_slice basis) (fun _ => power)
        [rangeCursor iter.start.val] acc = .ok accNext := by
  obtain ⟨nextIter, hnext, hstart, hend, hroom⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hlt
  have hmax : Usize.max + 1 = 2^UScalarTy.Usize.numBits := Usize.max_succ_eq_pow
  have hcurBound : iter.start.val < 2^UScalarTy.Usize.numBits := by omega
  have hnextBound : iter.start.val + 1 < 2^UScalarTy.Usize.numBits := by omega
  have hcurVal := rangeCursor_val iter.start.val hcurBound
  have hnextVal := rangeCursor_val (iter.start.val + 1) hnextBound
  have hindexEq : rangeCursor iter.start.val = iter.start := by
    apply UScalar.eq_of_val_eq
    rw [hcurVal]
  have hnextCursor : nextIter.start = rangeCursor (iter.start.val + 1) := by
    apply UScalar.eq_of_val_eq
    rw [hstart, hnextVal]
  have hstep : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some (rangeCursor iter.start.val), nextIter) := by
    simpa [hindexEq] using hnext
  have hbody := push_query_loop_body_matches_single_row power basis iter nextIter acc accNext
      (rangeCursor iter.start.val) basisValue hstep hread hpush
  exact ⟨nextIter, hstep, hnextCursor, hbody.1, hbody.2⟩


#print axioms indexed_loop_step_matches_model

end BatchedWeightsPushQueryGeneratedBridgeV7
