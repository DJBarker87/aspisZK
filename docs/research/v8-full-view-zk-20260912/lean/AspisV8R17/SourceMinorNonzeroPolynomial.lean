import AspisV8R17.SourceMinorPolynomial
import AspisV8R17.SourceMinorDeterminant

/-! Nonzero concrete determinant polynomial from the checked algebraic
witness. No sampler, random-oracle law or security loss is asserted. -/
set_option autoImplicit false
namespace AspisV8R17.SourceMinor
noncomputable section
open MvPolynomial
local instance : Fact (1 < (2147483647 : ℕ)) := ⟨by decide⟩

def fixedMinorPolynomial : ActivePoly (ZMod 2147483647) :=
  (polynomialMinor (1073741824 : ZMod 2147483647)).det

theorem fixedMinorPolynomial_eval_ne_zero :
    eval (activeAssignment 2 3 4) fixedMinorPolynomial ≠ 0 := by
  unfold fixedMinorPolynomial
  rw [polynomialMinor_det_eval]
  rw [show 1+(3 : ZMod 2147483647)*4 = 13 from by decide,
      show (3 : ZMod 2147483647)*4-1 = 11 from by decide,
      show -((3 : ZMod 2147483647)+4) = -7 from by decide]
  exact Windows.source_minor_det_ne_zero

theorem fixedMinorPolynomial_ne_zero : fixedMinorPolynomial ≠ 0 := by
  intro h
  apply fixedMinorPolynomial_eval_ne_zero
  rw [h, map_zero]

theorem fixedMinorPolynomial_degree : fixedMinorPolynomial.totalDegree ≤ 1070 :=
  polynomialMinor_det_degree _

#print axioms fixedMinorPolynomial_eval_ne_zero
#print axioms fixedMinorPolynomial_ne_zero
#print axioms fixedMinorPolynomial_degree
end
end AspisV8R17.SourceMinor
