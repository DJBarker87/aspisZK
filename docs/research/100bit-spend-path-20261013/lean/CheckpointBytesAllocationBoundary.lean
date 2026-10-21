import OraclePortCkptAbi5Weights

set_option autoImplicit false
namespace AspisR1.CheckpointBytesAllocationBoundary
open Aeneas Aeneas.Std Result

/-- Even perfectly decoded values cannot force a failed reservation to succeed.
This is the explicit inherited fallible model, not physical allocator adoption. -/
theorem reservation_rejection {T : Type} (n : Usize) (zero : T) (values : List T) :
    OraclePortCkptAbi5Weights.allocatedOverwrite n zero false values =
      ok (.error .allocation) := rfl

/-- No all-reservation-state successful roundtrip exists for this model step. -/
theorem no_unconditional_success {T : Type} (n : Usize) (zero : T) (values : List T) :
    ¬ ∀ reserved : Bool, ∃ out,
      OraclePortCkptAbi5Weights.allocatedOverwrite n zero reserved values =
        ok (.ok out) := by
  intro all
  obtain ⟨out,h⟩ := all false
  rw [reservation_rejection] at h
  cases h

#print axioms reservation_rejection
#print axioms no_unconditional_success
end AspisR1.CheckpointBytesAllocationBoundary
