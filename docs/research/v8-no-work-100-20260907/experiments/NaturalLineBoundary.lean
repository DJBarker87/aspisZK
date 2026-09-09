import ChordPolynomialImage

/-! Generic sparse natural-line boundary lemmas, compiled before any
concrete selected-width specialization. -/
set_option autoImplicit false
set_option maxRecDepth 100
set_option maxHeartbeats 100000
namespace AspisV8.NaturalChordImage
noncomputable section
open Polynomial AspisCircleTensorBinding AspisV8.ChordPolynomialImage
variable {K : Type*} [Field K] [NeZero (2:K)]

def line {m : Nat} (v : Fin m → K) : K[X] :=
  ∑ j, C (v j)*naturalLinePoly K j.val

theorem line_degree {n : Nat} (v : Fin (n+1) → K) :
    (line v).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans (by rw [naturalLinePoly_natDegree]; omega)

theorem line_top {n : Nat} (v : Fin (n+1) → K) :
    (line v).coeff n = v (Fin.last n)*(naturalLinePoly K n).leadingCoeff := by
  classical
  rw [line, finsetSum_coeff]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [coeff_C_mul]
    congr 1
    change (naturalLinePoly K n).coeff n=(naturalLinePoly K n).leadingCoeff
    rw [leadingCoeff, naturalLinePoly_natDegree]
  · intro j _ hj
    have lt : j.val < n := by
      have ne : j.val ≠ n := by intro eq; apply hj; exact Fin.ext eq
      omega
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [naturalLinePoly_natDegree]; exact lt), mul_zero]
  · intro h; exact False.elim (h (Finset.mem_univ _))

theorem line_next {n : Nat} (v : Fin (n+2) → K) (top : v (Fin.last (n+1))=0) :
    (line v).coeff n = v ⟨n,by omega⟩*(naturalLinePoly K n).leadingCoeff := by
  have split : line v = line (fun j : Fin (n+1) => v j.castSucc) := by
    rw [line, Fin.sum_univ_castSucc]
    simp only [top, C_0, zero_mul, add_zero]
    rfl
  rw [split, line_top]
  rfl

/-- Symbolic low-bit carry, BEFORE specializing to any large basis index.
Concrete unfolding at 511 caused a bounded failed preflight; this recurrence
keeps Chebyshev products abstract throughout elaboration and checking. -/
theorem basis_low_bit (n : Nat) :
    naturalLinePoly K (2*n+1) = X*naturalLinePoly K (2*n) := by
  simp only [naturalLinePoly, Nat.bitIndices_two_mul_add_one,
    Nat.bitIndices_two_mul, List.toFinset_cons]
  have notmem : 0 ∉ ((n.bitIndices).map (fun i => i+1)).toFinset := by simp
  rw [Finset.prod_insert notmem]
  simp only [pow_zero, Nat.cast_one, Polynomial.Chebyshev.T_one]

theorem leading_low_bit (n : Nat) :
    (naturalLinePoly K (2*n+1)).leadingCoeff = (naturalLinePoly K (2*n)).leadingCoeff := by
  rw [basis_low_bit, leadingCoeff_mul, leadingCoeff_X, one_mul]

#print axioms line_degree
#print axioms line_top
#print axioms line_next
#print axioms basis_low_bit
#print axioms leading_low_bit
end
end AspisV8.NaturalChordImage
