import Stage2ContinuationQueryAdvance

/-! An obstruction in the ACTUAL typed continuation API, not a source bug.
Arbitrary backend records do not imply checked totality from field/index bounds.
This file does not change a soundness endpoint or add an assumption to one. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.R22OverflowWorkerBackendObstruction
open AspisR1Stage2

theorem accumulate_forced_overflow
    (ops : AccumulateOps) (p : verifier.Prepared) (a : verifier.Accumulator)
    (node : Stage2M) (value : Stage2E) (weights : verifier.BatchedWeights) :
    verifier.accumulateWithOps {ops with zero := fail .integerOverflow}
      p a node value weights = fail .integerOverflow := by
  simp only [verifier.accumulateWithOps, bind_tc_fail]

theorem cannot_infer_backend_totality
    (ops : AccumulateOps) (p : verifier.Prepared) (a : verifier.Accumulator)
    (node : Stage2M) (value : Stage2E) (weights : verifier.BatchedWeights) :
    ¬ (∀ backend : AccumulateOps, ∃ out,
      verifier.accumulateWithOps backend p a node value weights = ok out) := by
  intro h
  obtain ⟨out,hout⟩ := h {ops with zero := fail .integerOverflow}
  rw [accumulate_forced_overflow] at hout
  cases hout

#print axioms accumulate_forced_overflow
#print axioms cannot_infer_backend_totality
end AspisR1.R22OverflowWorkerBackendObstruction
