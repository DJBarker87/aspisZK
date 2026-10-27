import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_FoldLinear
open scoped BigOperators
variable {E I : Type} [Field E] [Fintype I]

theorem one {n : Nat} (a : E) (c : I → E) (rows : I → Fin (4*n) → E) (i : Fin n) :
    RoundPairing.dualFold a (fun j=>∑ k,c k*rows k j) i=
      ∑ k,c k*RoundPairing.dualFold a (rows k) i := by
  unfold RoundPairing.dualFold
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem two (a0 a1 : E) (c : I → E) (rows : I → Fin 1024 → E) (i : Fin 64) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (fun j=>∑ k,c k*rows k j)) i=
      ∑ k,c k*RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (rows k)) i := by
  simp_rw [one]

theorem value (a0 a1 : E) (c : I → E) (rows : I → Fin 1024 → E) (f : Fin 64 → E) :
    (∑ k,c k*RoundPairing.dot f (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (rows k))))=
      RoundPairing.dot f (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (fun j=>∑ k,c k*rows k j))) := by
  unfold RoundPairing.dot
  simp_rw [two,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms one
#print axioms two
#print axioms value
end AspisR1.FJr_FoldLinear
end
