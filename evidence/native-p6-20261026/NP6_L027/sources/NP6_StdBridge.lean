import NP6_ClaimsModel
import Port3_Constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_StdBridge
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent

theorem map_error {T E F O : Type} (f : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (state : O) :
    mapError f r state = Port3_Constructor.core.result.Result.map_err f r state := by
  cases r <;> rfl

theorem box_array_contents {T : Type} (n : Usize) (before : Slice T) (out : Array T n)
    (returned : boxArray n before = ok (.Ok out)) : out.val = before.val := by
  unfold boxArray at returned
  split at returned
  · have same := core.result.Result.Ok.inj (Result.ok.inj returned)
    cases same
    rfl
  · cases returned

/-- The existing allocator outcome is mapped before any decoder continuation.
This handles the fallible branch of the complete emitted reference; it does
not assert that Kani's default Rust allocator can generate a null return. -/
theorem allocation_failure (error : NP6_StdModel.ReserveError)
    (pre : r1_wire.Prefix) (vr : Record)
    (getter : (ClaimsUnrolledFinish.external (NP6_StdModel.calls (.Err error))).validated pre 25#u8 =
      ok (.Ok vr)) :
    claimsReference (ClaimsUnrolledFinish.external (NP6_StdModel.calls (.Err error))) pre =
      ok (.Err .Allocation) := by
  rw [NP6_ClaimsModel.reference_normalized]
  simp [NP6_ClaimsModel.normalized,getter]

#print axioms map_error
#print axioms box_array_contents
#print axioms allocation_failure
end AspisR1.NP6_StdBridge
end
