import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1S9CandidateUpdateMapV1

/-- Successful fixed-index array writes commute with a pointwise carrier map.
The index bound is explicit, and the result is the same mapped written array. -/
theorem mapArray_update_success {α β : Type} {n : Usize}
    (f : α → β) (a : Array α n) (i : Usize) (x : α)
    (hi : i.val < n.val) (out : Array α n)
    (h : Array.update a i x = .ok out) :
    ∃ out', Array.update (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a)
      i (f x) = .ok out' ∧
      AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f out = out' := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨updated, hu, hset⟩ := WP.spec_imp_exists (Array.update_spec a i x hlen)
  have hout : out = updated := Result.ok.inj (h.symm.trans hu)
  subst out
  have hlen' : i.val < (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a).length := by
    simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapArray, a.property] using hi
  obtain ⟨updated', hu', hset'⟩ := WP.spec_imp_exists
    (Array.update_spec (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a)
      i (f x) hlen')
  have hsetMap : AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f updated = updated' := by
    rw [hset, hset']
    apply Subtype.ext
    simp [AspisR1S9CandidateFoldMapPrimitivesV1.mapArray,
      Array.set_val_eq, List.map_set]
  exact ⟨updated', hu', hsetMap⟩

#print axioms mapArray_update_success

end AspisR1S9CandidateUpdateMapV1
