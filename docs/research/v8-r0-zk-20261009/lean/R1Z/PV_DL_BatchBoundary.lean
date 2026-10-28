import R1Z.PV_DL_CompressionTrace
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_BatchBoundary
set_option autoImplicit false

/-- Diagnostic callback which observes batching; it is not a SHA backend. -/
def observeBatch (state : Nat) (batch : List Unit) : Result Nat :=
  ok (state+batch.length*batch.length)

/-- Two singleton calls cannot replace one two-block call for an arbitrary
batched callback. Retain the byte-fold model only under a proved fold law. -/
theorem boundary_counterexample :
    PV_DL_CompressionTrace.run observeBatch [[(),()]] 0 ≠
      PV_DL_CompressionTrace.run observeBatch [[()],[()]] 0 := by
  simp [PV_DL_CompressionTrace.run,observeBatch,bind_tc_ok]

#print axioms observeBatch
#print axioms boundary_counterexample
end R1Z.PV_DL_BatchBoundary
