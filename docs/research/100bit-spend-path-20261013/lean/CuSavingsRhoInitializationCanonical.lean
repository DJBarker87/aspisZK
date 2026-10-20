import CuSavingsRhoHeap
import CuSavingsRhoResumeLoans

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoInitializationCanonical
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoVector CuSavingsRhoFinishModel
open CuSavingsRhoResumeLoans

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem canonical_members (weights : Slice field.QM31) (hc : CanonicalFrom weights 0) :
    ∀ value ∈ weights.val,Canonical value := by
  intro value hv
  obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp hv
  rw [← heq]
  exact hc i hi (Nat.zero_le _)

variable [HeapReserve]

/-- Whole actual new/zip wrapper using the whole actual heap helper. Its
successful state has the complete starting invariant; no heap-child length or
success premise is supplied. Canonical input is obtained from the actual
constructor or resumed-weight source theorems at the callers. -/
theorem source_success (weights : Slice field.QM31) (hc : CanonicalFrom weights 0)
    (out : verifier.BatchedWeights)
    (h : @verifier.BatchedWeights.new CuSavingsRhoHeap.sourceAllocator weights = .ok (.Ok out)) :
    out=initialState weights ∧ Good out [] ∧ canonicalSlice out=weights ∧
      out.terms.val=0 ∧ out.raw.val.length=weights.val.length := by
  letI : InitAllocation := CuSavingsRhoHeap.sourceAllocator
  change verifier.BatchedWeights.new weights = .ok (.Ok out) at h
  rw [← CuSavingsRhoInitSource.source_eq,CuSavingsRhoHeap.initializer_outcome] at h
  obtain ⟨result,_,h⟩ := bind_ok _ _ _ h
  cases result with
  | Err error => cases h
  | Ok raw =>
    simp only [CuSavingsRhoInitSource.heapOutcome] at h
    have heq := core.result.Result.Ok.inj (Result.ok.inj h)
    cases heq
    refine ⟨rfl,CuSavingsRhoBatches.initial_good weights (canonical_members weights hc),
      CuSavingsRhoBatches.initial_projection weights (canonical_members weights hc),?_,?_⟩
    · change (0#usize).val=0
      scalar_tac
    · simp only [initialState,List.length_map]

#print axioms canonical_members
#print axioms source_success
end AspisR1.CuSavingsRhoInitializationCanonical
