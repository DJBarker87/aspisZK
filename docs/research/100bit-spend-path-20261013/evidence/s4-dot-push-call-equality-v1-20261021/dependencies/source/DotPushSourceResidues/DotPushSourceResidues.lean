import DotPushFourCoordinates
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DotPushLocal.Proof

def updatedSums (s r : Array U64 4#usize) : Array U64 4#usize :=
  ⟨List.zipWith updateWord s.val r.val,by
    rw [List.length_zipWith,s.property,r.property]
    rfl⟩

theorem push_total_from_raw
    (rawFn : canonical.Q → canonical.Q → Result (Array U64 4#usize))
    (self : canonical.Dot) (left right : canonical.Q) (raw : Array U64 4#usize)
    (hraw : rawFn left right = .ok raw) :
    canonical.Dot.push rawFn self left right = .ok ⟨updatedSums self.sums raw⟩ := by
  cases self with
  | mk sums =>
    obtain ⟨a,b,c,d,hs⟩ := List.length_eq_four.mp sums.property
    obtain ⟨r0,r1,r2,r3,hr⟩ := List.length_eq_four.mp raw.property
    have hs' : sums=Array.make 4#usize [a,b,c,d] := Subtype.ext hs
    have hr' : raw=Array.make 4#usize [r0,r1,r2,r3] := Subtype.ext hr
    subst sums
    subst raw
    exact push_four_coordinates rawFn left right a b c d r0 r1 r2 r3 hraw

theorem updatedSums_residue
    (s r : Array U64 4#usize)
    (hs : ∀ x ∈ s.val, x.val < 2 ^ 46)
    (j : Nat) (hj : j<4) :
    ((updatedSums s r).val[j]'(by rw [(updatedSums s r).property];exact hj)).val %
          AspisR1EbyKDotPushNatStep.modulus =
      ((s.val[j]'(by rw [s.property];exact hj)).val +
       (r.val[j]'(by rw [r.property];exact hj)).val) % AspisR1EbyKDotPushNatStep.modulus := by
  have hjS : j<s.val.length := by rw [s.property];exact hj
  have hjR : j<r.val.length := by rw [r.property];exact hj
  have hbound := hs (s.val[j]'hjS) (List.getElem_mem hjS)
  have hv := (updateWord_value (s.val[j]'hjS) (r.val[j]'hjR) hbound).2
  simpa only [updatedSums,List.getElem_zipWith] using hv

#print axioms push_total_from_raw
#print axioms updatedSums_residue
end AspisR1DotPushLocal.Proof
