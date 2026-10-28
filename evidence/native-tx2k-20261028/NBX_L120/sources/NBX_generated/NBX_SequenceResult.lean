import NBX_SequenceDomains
import NBX_PredicateScan
set_option autoImplicit false
namespace NBX_SequenceResult
open Aeneas Aeneas.Std Result

/-- Observe precisely the rows assigned by the native one-step model. Their
returned sequence is independent of the arbitrary initial accumulator. -/
theorem returned (read : Nat → U64) (start count : Nat) (initial : Nat → U64) :
    (List.range count).map
      (fun k => NBX_RowFrames.writeRows read start count initial (start+k)) =
    NBX_FrameComposition.sequenceRows read start count := by
  rw [NBX_FrameComposition.rows_value]
  apply List.map_congr_left
  intro k hk
  have index := List.mem_range.mp hk
  rw [NBX_RowFrames.value_frame]
  have inside : start ≤ start+k ∧ start+k < start+count := by omega
  rw [if_pos inside]

/-- Value-level representability needs equality only at the passed row reads;
initial accumulator values cannot affect the returned sequence. The native
reader/iterator/allocator correspondence is deliberately a separate gate. -/
theorem argument_frame (read other : Nat → U64) (start count : Nat)
    (initial otherInitial : Nat → U64)
    (same : ∀ k, start ≤ k → k < start+count → read k = other k) :
    (List.range count).map
      (fun k => NBX_RowFrames.writeRows read start count initial (start+k)) =
    (List.range count).map
      (fun k => NBX_RowFrames.writeRows other start count otherInitial (start+k)) := by
  rw [returned,returned]
  exact NBX_FrameComposition.rows_ext read other start count same

/-- The actual capacity predicate sees those same original-reader values after
row assembly; no successful scan, canonical input or initial-state premise. -/
theorem capacity (read : Nat → U64) (start count : Nat) (initial : Nat → U64) :
    NBX_PredicateScan.run (fun n : U64 => decide (1048576#u64 < n)) false
      ((List.range count).map
        (fun k => NBX_RowFrames.writeRows read start count initial (start+k))) =
    (List.range count).any (fun k => decide (1048576#u64 < read (start+k))) := by
  rw [returned]
  exact NBX_PredicateScan.capacity read start count

#print axioms returned
#print axioms argument_frame
#print axioms capacity
end NBX_SequenceResult
