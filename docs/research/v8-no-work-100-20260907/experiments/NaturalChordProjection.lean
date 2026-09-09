import NaturalChordImage
import NaturalProjectionCore

/-! Total natural-coordinate projection of chord multiplication.  The
conversion matrix is the inverse whose nonsingularity is already proved for
every width; there is no rank or successful-recovery premise.  Projection is
in natural coordinates, not in monomial coefficients. -/
set_option autoImplicit false
namespace AspisV8.NaturalChordProjection
noncomputable section
open Polynomial Matrix AspisCircleTensorBinding
open AspisV5FriConcreteEncoderApplicability
open AspisV8.ChordPolynomialImage AspisV8.NaturalChordImage
variable {K : Type*} [Field K] [NeZero (2 : K)]

def fullEven (a b c : K) (q : Fin 1024 → K) : K[X] :=
  evenPart a b c (line (even q)) (line (odd q))
def fullOdd (a b c : K) (q : Fin 1024 → K) : K[X] :=
  oddPart a b c (line (even q)) (line (odd q))
def projectedEven (a b c : K) (q : Fin 1024 → K) : Fin 512 → K :=
  projectLine 512 2 (fullEven a b c q)
def projectedOdd (a b c : K) (q : Fin 1024 → K) : Fin 512 → K :=
  projectLine 512 2 (fullOdd a b c q)

theorem full_pair_degree (a b c : K) (q : Fin 1024 → K) :
    (fullEven a b c q).natDegree ≤ 513 ∧ (fullOdd a b c q).natDegree ≤ 513 := by
  have az := natDegree_le_iff_coeff_eq_zero.mp (line_degree (even q))
  have bz := natDegree_le_iff_coeff_eq_zero.mp (line_degree (odd q))
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
    rw [fullEven, Nat.add_comm 2 r, even_coeff]
    simp [az (r+2) (by omega), az (r+1) (by omega),
      bz (r+2) (by omega), bz r (by omega)]
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m by omega)
    rw [fullOdd, Nat.add_comm 1 r, odd_coeff]
    simp [az (r+1) (by omega), bz (r+1) (by omega), bz r (by omega)]

/-- Width 514 captures the *whole* multiplication result, even when the
image constraints fail. Only the subsequent natural prefix discards data. -/
theorem full_pair_representation (a b c : K) (q : Fin 1024 → K) :
    naturalCoefficientPolynomial (coefficients 514 (fullEven a b c q))=fullEven a b c q ∧
      naturalCoefficientPolynomial (coefficients 514 (fullOdd a b c q))=fullOdd a b c q := by
  have degree := full_pair_degree a b c q
  exact ⟨coefficients_polynomial (by omega) _ degree.1,
    coefficients_polynomial (by omega) _ degree.2⟩

theorem selected_projected_pair (a b c : K) (q : Fin 1024 → K)
    (chord : b ≠ 0 ∨ c ≠ 0)
    (image : q 1023=0 ∧ b*q 1022-c*q 1021=0) :
    naturalCoefficientPolynomial (projectedEven a b c q)=fullEven a b c q ∧
      naturalCoefficientPolynomial (projectedOdd a b c q)=fullOdd a b c q := by
  have degree := (selected_image_iff a b c q chord).mpr image
  exact ⟨projectLine_polynomial (by omega) _ degree.1,
    projectLine_polynomial (by omega) _ degree.2⟩

theorem selected_projected_circle_eval (a b c x y : K) (q : Fin 1024 → K)
    (chord : b ≠ 0 ∨ c ≠ 0)
    (image : q 1023=0 ∧ b*q 1022-c*q 1021=0)
    (circle : x^2+y^2=1) :
    circleEval (naturalCoefficientPolynomial (projectedEven a b c q))
      (naturalCoefficientPolynomial (projectedOdd a b c q)) x y =
      (a+b*x+c*y)*circleEval (line (even q)) (line (odd q)) x y := by
  obtain ⟨he,ho⟩ := selected_projected_pair a b c q chord image
  rw [he,ho]
  exact chord_eval a b c x y _ _ circle

#print axioms full_pair_degree
#print axioms full_pair_representation
#print axioms selected_projected_pair
#print axioms selected_projected_circle_eval
end
end AspisV8.NaturalChordProjection
