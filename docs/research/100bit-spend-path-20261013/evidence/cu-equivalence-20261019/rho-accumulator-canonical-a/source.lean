import CuSavingsRhoHeapValues
import CuSavingsRhoAccumulatorNew

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoAccumulatorCanonical
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRhoEmptyReserveModel CuSavingsRhoAccumulatorNew

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem zero_canonical : CuSavingsRhoPowerTail.Canonical aspis_core.field.QM31.ZERO := by
  rw [aspis_core.field.QM31.ZERO]
  change ((0#u32).val < 2147483647 ∧ (0#u32).val < 2147483647) ∧
    ((0#u32).val < 2147483647 ∧ (0#u32).val < 2147483647)
  constructor <;> constructor <;> scalar_tac

/-- Whole source constructor, now with the original reserve wrapper's empty
frame discharged. No reserve-success or vector-content premise is supplied. -/
theorem source_values (backend : Backend) (variant : transport.Variant)
    (out : verifier.Accumulator)
    (h : @verifier.Accumulator.new (heapReserve backend) variant = .ok (.Ok out)) :
    out.weights.val=List.replicate (length variant).val aspis_core.field.QM31.ZERO ∧
    ∀ (i : Nat) (hi : i<out.weights.val.length),
      CuSavingsRhoPowerTail.Canonical (out.weights.val[i]'hi) := by
  letI : AspisR1CuRho.HeapReserve := heapReserve backend
  change verifier.Accumulator.new variant = .ok (.Ok out) at h
  rw [CuSavingsRhoAccumulatorNew.source_outcome] at h
  obtain ⟨result,hheap,h⟩ := bind_ok _ _ _ h
  cases result with
  | Err error => cases h
  | Ok weights =>
    have hvalues := CuSavingsRhoHeapValues.source_values backend
      aspis_core.field.QM31.Insts.CoreMarkerCopy (length variant)
      aspis_core.field.QM31.ZERO weights (by rfl) hheap
    have heq := core.result.Result.Ok.inj (Result.ok.inj h)
    cases heq
    refine ⟨hvalues,?_⟩
    intro i hi
    change CuSavingsRhoPowerTail.Canonical (weights.val[i]'hi)
    rw [hvalues,List.getElem_replicate]
    exact zero_canonical

#print axioms zero_canonical
#print axioms source_values
end AspisR1.CuSavingsRhoAccumulatorCanonical
