import BatchedWeightsIndexedQueryLoopModelV18
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV4
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

end BatchedWeightsPushQueryGeneratedBridgeV4
