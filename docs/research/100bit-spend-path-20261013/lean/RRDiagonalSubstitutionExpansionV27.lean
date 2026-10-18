import RRActualBivariateTaylorBridgeV8
open Polynomial
noncomputable section
namespace RRActualBivariateTaylorBridge
variable {K : Type*} [CommSemiring K]

def diagonalExpansion (p : K[X]) (a : K) : Bivariate K :=
  (Polynomial.map (C : K →+* Polynomial K) (Polynomial.taylor a p)).sum
    fun j c => C c * ((X : Bivariate K) * C (X : Polynomial K)) ^ j

theorem substitution_eq_diagonalExpansion (p : K[X]) (a : K) :
    substituteByChild p a = diagonalExpansion p a := by
  rw [lift_taylor_substitution]
  unfold diagonalExpansion
  simp [Polynomial.comp, Polynomial.eval₂_eq_sum]

lemma coeff_diagTerm (c : Polynomial K) (i j : Nat) :
    (C c * ((X : Bivariate K) * C (X : Polynomial K)) ^ i : Bivariate K).coeff j =
      if j = i then c * (X : Polynomial K)^i else 0 := by
  have hp : ((X : Bivariate K) * C (X : Polynomial K)) ^ i =
      C ((X : Polynomial K)^i) * (X : Bivariate K)^i := by
    rw [mul_comm (X : Bivariate K) (C (X : Polynomial K)), mul_pow]
    simp
  rw [hp, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]

lemma coeff_diagonalExpansion (p : K[X]) (a : K) (j : Nat) :
    (diagonalExpansion p a).coeff j =
      C ((Polynomial.taylor a p).coeff j) * (X : Polynomial K)^j := by
  unfold diagonalExpansion
  rw [Polynomial.coeff_sum]
  simp only [coeff_diagTerm]
  rw [Polynomial.sum_def]
  have hTaylor :
      Polynomial.taylor (C a) (liftCoeffPolynomial p) =
        Polynomial.map (C : K →+* Polynomial K) (Polynomial.taylor a p) := by
    unfold liftCoeffPolynomial
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply]
    rw [Polynomial.map_comp]
    simp
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, Polynomial.coeff_map]
  · intro b hb hbj
    have hji : j ≠ b := fun h => hbj h.symm
    rw [if_neg hji]
  · intro hj
    have hz : ((Polynomial.map (C : K →+* Polynomial K) (Polynomial.taylor a p)).coeff j) = 0 :=
      Polynomial.notMem_support_iff.mp hj
    have hTaylorMap :
        Polynomial.taylor (C a) (Polynomial.map (C : K →+* Polynomial K) p) =
          Polynomial.map (C : K →+* Polynomial K) (Polynomial.taylor a p) := by
      simpa [liftCoeffPolynomial] using hTaylor
    have hzeroTarget :
        (Polynomial.taylor (C a) (Polynomial.map (C : K →+* Polynomial K) p)).coeff j = 0 := by
      rw [hTaylorMap, Polynomial.coeff_map]
      simpa only [Polynomial.coeff_map] using hz
    simp [hzeroTarget]

theorem coeff_inner_substitution (p : K[X]) (a : K) (j : Nat) :
    (substituteByChild p a).coeff j =
      C ((Polynomial.taylor a p).coeff j) * (X : Polynomial K)^j := by
  rw [substitution_eq_diagonalExpansion, coeff_diagonalExpansion]

#print axioms coeff_inner_substitution
end RRActualBivariateTaylorBridge
