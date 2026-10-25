import S8Kani2CallerJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.RowFinish_Finalization
open Aeneas Aeneas.Std Result
open S8OwnedP6ValueModel S8OwnedP6Finish S8Kani2MutableValue
open S8Kani2FinishReferenceJoin S8Kani2MutableExtraction.batched_weights

/-- The actual returned slice, rather than a separately selected successful
finalization, has the certified reference cells. No canonical raw-row bound
or phase bound is required. This is batched-weight finalization, not op19. -/
theorem returned (raw : Raw) (old : Weights) (terms : Usize)
    (out : FinishSlice) (lengths : old.length ≤ raw.length)
    (source : BatchedWeights.finish (⟨raw,terms⟩ : F.BW) (toSlice old) = ok out) :
    ∃ referenceOut : Weights,
      S8OwnedP6.finish_owned raw old = ok referenceOut ∧
      referenceOut.length = old.length ∧
      ∀ j : Usize, j.val < old.length → ∃ row : Row,
        raw.val[j.val]? = some row ∧
        referenceOut.val[j.val]? = some (modelValue row) ∧
        Slice.index_usize out j = ok (toFinish (modelValue row)) := by
  obtain ⟨referenceOut,certified,reference,length,simulation,cells⟩ :=
    S8Kani2CallerJoin.p6_certificate.finish_simulation raw old terms lengths
  have same : certified = out := Result.ok.inj (simulation.symm.trans source)
  subst certified
  exact ⟨referenceOut,reference,length,cells⟩

#print axioms returned
end AspisR1.RowFinish_Finalization
end
