import AspisFormal.V5FriConcreteEncoderApplicability

/-! Generic natural-coordinate conversion and prefix adjoint. Compiled before
the concrete selected chord specialization. No rank premise or field
enumeration; nonsingularity is inherited from the proved triangular basis. -/
set_option autoImplicit false
namespace AspisV8.NaturalChordProjection
noncomputable section
open Polynomial Matrix AspisCircleTensorBinding
open AspisV5FriConcreteEncoderApplicability
variable {K : Type*} [Field K] [NeZero (2 : K)]

def coefficients (m : Nat) (p : K[X]) : Fin m → K :=
  monomialToNatural K m *ᵥ (fun i => p.coeff i)

theorem coefficients_polynomial {m : Nat} (hm : 0 < m) (p : K[X])
    (hp : p.natDegree ≤ m-1) :
    naturalCoefficientPolynomial (coefficients m p) = p := by
  unfold naturalCoefficientPolynomial naturalToMonomialCoefficients coefficients
  rw [Matrix.mulVec_mulVec, naturalCoeff_mul_monomialToNatural, Matrix.one_mulVec]
  ext j
  by_cases hj : j < m
  · exact monomialPolynomial_coeff _ ⟨j,hj⟩
  · rw [monomialPolynomial_coeff_eq_zero_of_ge _ j (by omega)]
    exact (coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega))).symm

def pad {n : Nat} (r : Nat) (v : Fin n → K) : Fin (n+r) → K :=
  Fin.addCases v (fun _ => 0)

def takePrefix {n r : Nat} (v : Fin (n+r) → K) : Fin n → K :=
  fun i => v (i.castAdd r)

@[simp] theorem prefix_pad {n r : Nat} (v : Fin n → K) : takePrefix (pad r v)=v := by
  funext i
  simp [takePrefix,pad]

theorem polynomial_pad {n r : Nat} (hn : 0<n) (v : Fin n → K) :
    naturalCoefficientPolynomial (pad r v)=naturalCoefficientPolynomial v := by
  rw [naturalCoefficientPolynomial_eq_basisSum (by omega),
    naturalCoefficientPolynomial_eq_basisSum hn, Fin.sum_univ_add]
  simp [pad]

theorem coefficients_eq_pad {n r : Nat} (hn : 0<n) (p : K[X])
    (hp : p.natDegree ≤ n-1) (v : Fin n → K)
    (hv : naturalCoefficientPolynomial v=p) :
    coefficients (n+r) p=pad r v := by
  apply naturalCoefficientPolynomial_injective
  rw [coefficients_polynomial (by omega) p (by omega), polynomial_pad hn, hv]

/-- Total conversion at the extended width, then natural-coordinate prefix.
It is intentionally not monomial truncation. -/
def projectLine (n r : Nat) (p : K[X]) : Fin n → K :=
  takePrefix (coefficients (n+r) p)

theorem projectLine_polynomial {n r : Nat} (hn : 0<n) (p : K[X])
    (hp : p.natDegree ≤ n-1) :
    naturalCoefficientPolynomial (projectLine n r p)=p := by
  obtain ⟨v,hv⟩ := naturalCoefficientPolynomial_complete hn p hp
  unfold projectLine
  rw [coefficients_eq_pad hn p hp v hv, prefix_pad, hv]

/-- The zero-padded covector is adjoint to the actual natural prefix. -/
theorem prefix_dot {n r : Nat} (w : Fin n → K) (v : Fin (n+r) → K) :
    (∑ i, w i*takePrefix v i) = ∑ i, pad r w i*v i := by
  rw [Fin.sum_univ_add]
  simp [pad,takePrefix]

#print axioms coefficients_polynomial
#print axioms polynomial_pad
#print axioms coefficients_eq_pad
#print axioms projectLine_polynomial
#print axioms prefix_dot
end
end AspisV8.NaturalChordProjection
