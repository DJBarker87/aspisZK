import S8OwnedP6Finish
import BatchedWeightsActualReducer

/-! Instantiation points for R14's reducer and finalized-weights model.
The caller's weighted-sum invariant is explicit; it is owned by S7/R15. -/
set_option autoImplicit false
noncomputable section
namespace S8OwnedP6R14Backend
open Aeneas Aeneas.Std Result
open S8OwnedP6ValueModel S8OwnedP6Finish

/-- Supplies the precise reducer equality called repin_S8 by
Stage2FinishReducer, for this freshly emitted concrete implementation. -/
theorem reducer_repin (x : U64) :
    S8OwnedP6.aspis_core.field.M31.reduce_u64 x=
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x :=
  (S8OwnedP6ValueModel.reducer_eq x).trans
    (AspisR1.BatchedWeightsActualReducer.generated_wrapper_eq_current x).symm

/-- The entire emitted finalization loop transports a raw congruence invariant
to the intended canonical sums, at every row and every field coordinate. -/
theorem finish_sum_model (raw : Raw) (old : Weights) (sum : Nat → Fin 4 → Nat)
    (hlen : old.length≤raw.length)
    (residue : ∀ j row, raw.val[j]?=some row → ∀ k : Fin 4,
      (rowAt row k).val%2147483647=sum j k%2147483647) :
    ∃ out : Weights, S8OwnedP6.finish_owned raw old=.ok out ∧
      out.length=old.length ∧ ∀ j, j<old.length →
        ∃ row q, raw.val[j]?=some row ∧ out.val[j]?=some q ∧
          ∀ k : Fin 4, (coordinate q k).val=sum j k%2147483647 ∧
            (coordinate q k).val<2147483647 := by
  obtain ⟨out,hrun,hsize,hcells⟩ := finish_total_model raw old hlen
  refine ⟨out,hrun,hsize,?_⟩
  intro j hj
  have hr : j<raw.val.length := by change j<raw.length; omega
  let row := raw.val[j]'hr
  have hrow : raw.val[j]?=some row := List.getElem?_eq_getElem hr
  refine ⟨row,modelValue row,hrow,?_,?_⟩
  · simpa only [hrow,Option.map_some] using hcells j hj
  · intro k
    have h := modelValue_coordinates row k
    exact ⟨h.1.trans (residue j row hrow k),h.2⟩

#print axioms reducer_repin
#print axioms finish_sum_model
end S8OwnedP6R14Backend
