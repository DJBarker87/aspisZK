import R1FunctionalWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_GroupAlgebra
open scoped BigOperators
variable {K : Type} [CommSemiring K]
/-- Grouping coefficients by identical masks preserves their full sum. -/
theorem regroup {n g : Nat} (group : Fin n → Fin g) (f : Fin n → K) (w : Fin g → K) :
    (∑ k : Fin g, (∑ j : Fin n, if group j=k then f j else 0)*w k)=
      ∑ j : Fin n, f j*w (group j) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp
/-- Reordering finite challenge products does not alter the inactive pairing. -/
theorem distribute {n g s : Nat} (group : Fin n → Fin g) (f : Fin n → K)
    (selected : Fin g → Fin s → Bool) (low : Fin s → K) :
    (∑ k : Fin g, (∑ j : Fin n, if group j=k then f j else 0)*
      (∑ b : Fin s, if selected k b then low b else 0))=
    ∑ j : Fin n,∑ b : Fin s, if selected (group j) b then f j*low b else 0 := by
  rw [regroup]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  cases selected (group j) b <;> simp
#print axioms regroup
#print axioms distribute
end AspisR1.FJc_GroupAlgebra
end
