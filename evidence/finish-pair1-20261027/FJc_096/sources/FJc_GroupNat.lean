import FJc_GroupAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_GroupNat
open scoped BigOperators
/-- Group redistribution with abstract natural labels. Keep source table and
carrier elaboration outside this generic finite algebra kernel. -/
theorem distribute {K : Type} [CommSemiring K] {n g s : Nat}
    (label : Fin n → Nat) (bound : ∀ j,label j<g) (f : Fin n → K)
    (selected : Nat → Fin s → Bool) (low : Fin s → K) :
    (∑ k : Fin g,(∑ j : Fin n,if label j=k.val then f j else 0)*
      (∑ b : Fin s,if selected k.val b then low b else 0))=
    ∑ j : Fin n,∑ b : Fin s,if selected (label j) b then f j*low b else 0 := by
  let group : Fin n → Fin g := fun j=>⟨label j,bound j⟩
  have h := FJc_GroupAlgebra.distribute group f (fun k b=>selected k.val b) low
  simpa only [group,Fin.ext_iff] using h
#print axioms distribute
end AspisR1.FJc_GroupNat
end
