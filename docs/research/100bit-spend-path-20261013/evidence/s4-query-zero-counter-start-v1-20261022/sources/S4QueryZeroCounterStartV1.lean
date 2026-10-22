import Query31ExplicitListLoop
import R0C.V3.Q22Law
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4QueryZeroCounterStartV1

/-- Only the two counters determine the initial sampler projection. The
backing array may be any typed array: its empty accepted prefix is ignored. -/
theorem zero_counters_start
    (s : Query31ExplicitScanBody.CurrentScan)
    (hcount : s.accepted_len.val = 0) (hdraws : s.draws.val = 0) :
    Query31ExplicitScanBody.q22StateOf s = R0C.V3.Q22.q0 ∧
      Query31ExplicitListLoop.validState s := by
  constructor
  · simp only [Query31ExplicitScanBody.q22StateOf,
      Query31ExplicitScanBody.acceptedPrefix,hcount,hdraws,List.take_zero,List.map_nil]
    rfl
  · apply Query31ExplicitListLoop.validState_of_bounds s <;> omega

#print axioms zero_counters_start
end AspisR1.S4QueryZeroCounterStartV1
