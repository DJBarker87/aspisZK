import NaturalLineBoundary

/-! Sparse image claims in the selected y-low-bit natural circle basis.
Only the two final basis indices are reduced; no full tensor is enumerated. -/
set_option autoImplicit false
set_option maxRecDepth 100
set_option maxHeartbeats 100000
namespace AspisV8.NaturalChordImage
noncomputable section
open Polynomial AspisCircleTensorBinding AspisV8.ChordPolynomialImage
variable {K : Type*} [Field K] [NeZero (2:K)]

theorem final_basis_factor : naturalLinePoly K 511 = X*naturalLinePoly K 510 := by
  have h := basis_low_bit (K:=K) 255
  rw [show (2*255+1:Nat)=511 by decide, show (2*255:Nat)=510 by decide] at h
  exact h

#print axioms final_basis_factor

theorem final_leading_equal :
    (naturalLinePoly K 511).leadingCoeff = (naturalLinePoly K 510).leadingCoeff := by
  have h := leading_low_bit (K:=K) 255
  rw [show (2*255+1:Nat)=511 by decide, show (2*255:Nat)=510 by decide] at h
  exact h

#print axioms final_leading_equal

def even (q : Fin 1024 → K) : Fin 512 → K := fun j => q ⟨2*j.val,by omega⟩
def odd (q : Fin 1024 → K) : Fin 512 → K := fun j => q ⟨2*j.val+1,by omega⟩

/-- The two literal research claims, not substituted monomial coordinates. -/
theorem selected_image_iff (a b c : K) (q : Fin 1024 → K) (chord : b ≠ 0 ∨ c ≠ 0) :
    ((evenPart a b c (line (even q)) (line (odd q))).natDegree ≤ 511 ∧
      (oddPart a b c (line (even q)) (line (odd q))).natDegree ≤ 511) ↔
      q 1023=0 ∧ b*q 1022-c*q 1021=0 := by
  have lead : (naturalLinePoly K 511).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (naturalLinePoly_ne_zero 511)
  have At := line_top (even q)
  have Bt := line_top (odd q)
  have iff0 := image_iff a b c (line (even q)) (line (odd q)) 510
    (line_degree (even q)) (line_degree (odd q)) chord
  rw [iff0]
  have top_iff : (line (odd q)).coeff 511=0 ↔ q 1023=0 := by
    rw [Bt]
    change q 1023*(naturalLinePoly K 511).leadingCoeff=0 ↔ q 1023=0
    exact mul_eq_zero.trans (or_iff_left lead)
  constructor
  · rintro ⟨top,rel⟩
    have zero := top_iff.mp top
    have next := line_next (n:=510) (odd q) zero
    rw [At,next,← final_leading_equal] at rel
    change b*(q 1022*_)-c*(q 1021*_)=0 at rel
    refine ⟨zero,?_⟩
    apply (mul_eq_zero.mp (show (b*q 1022-c*q 1021)*(naturalLinePoly K 511).leadingCoeff=0 by
      linear_combination rel)).resolve_right lead
  · rintro ⟨zero,rel⟩
    refine ⟨top_iff.mpr zero,?_⟩
    have next := line_next (n:=510) (odd q) zero
    rw [At,next,← final_leading_equal]
    change b*(q 1022*_)-c*(q 1021*_)=0
    linear_combination (naturalLinePoly K 511).leadingCoeff*rel

#print axioms selected_image_iff
end
end AspisV8.NaturalChordImage
