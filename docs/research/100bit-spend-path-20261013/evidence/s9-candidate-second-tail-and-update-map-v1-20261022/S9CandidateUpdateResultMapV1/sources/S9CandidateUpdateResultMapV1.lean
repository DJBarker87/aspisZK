import S9CandidateUpdateMapV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CandidateUpdateResultMapV1
theorem mapArray_update_result {α β : Type} {n : Usize}
    (f : α → β) (a : Array α n) (i : Usize) (x : α)
    (hi : i.val < n.val) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f) (Array.update a i x) =
      Array.update (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a) i (f x) := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨out, hout, _⟩ := WP.spec_imp_exists (Array.update_spec a i x hlen)
  obtain ⟨out', hout', heq⟩ :=
    AspisR1S9CandidateUpdateMapV1.mapArray_update_success f a i x hi out hout
  rw [hout, hout']
  exact congrArg Result.ok heq
#print axioms mapArray_update_result
end AspisR1S9CandidateUpdateResultMapV1
