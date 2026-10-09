import LinearDenominatorPrimitive
import AspisFormal.K1.V7ExactCorrelatedAgreementSmooth

/-! A polynomial OOD answer for a positive-Z-degree denominator forces a
fixed leading-coefficient/resultant obstruction. Degrees in the resultant
are the ORIGINAL degrees, never silently replaced by specialized degrees. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.LinearDenominatorOOD
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementSmooth
noncomputable section
variable {K : Type*} [Field K]

def atPoint (A : Polynomial K[X]) (t : K) : K[X] :=
  A.map (Polynomial.evalRingHom t)

def certificate (A B : Polynomial K[X]) : K[X] :=
  A.leadingCoeff * Polynomial.resultant A B

theorem certificate_ne_zero (A B : Polynomial K[X]) (nonzero : A ≠ 0)
    (primitive : (C A * X + C B : Polynomial (Polynomial K[X])).IsPrimitive) :
    certificate A B ≠ 0 := by
  letI : NormalizedGCDMonoid K[X] := Nonempty.some inferInstance
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr nonzero)
    (LinearDenominatorPrimitive.resultant_ne_zero (L := FractionRing K[X])
      A B nonzero primitive)

/-- No root extension or separability premise is needed: the literal
polynomial identity and exact left degree suffice for the Sylvester proof. -/
theorem identity_resultant_zero (a b answer : K[X]) (m n : Nat)
    (positive : 0 < m) (leftDegree : a.natDegree = m)
    (rightDegree : b.natDegree ≤ n) (identity : a*answer+b=0) :
    Polynomial.resultant a b m n = 0 := by
  by_cases answerZero : answer = 0
  · have bZero : b = 0 := by simpa only [answerZero, mul_zero, zero_add] using identity
    rw [bZero, Polynomial.resultant_zero_right]
    simp only [zero_pow positive.ne', zero_mul]
  · have aNonzero : a ≠ 0 := by
      intro zero
      rw [zero, Polynomial.natDegree_zero] at leftDegree
      omega
    have bEq : b = -(a*answer) := eq_neg_of_add_eq_zero_right identity
    have productBound : answer.natDegree + m ≤ n := by
      rw [bEq, Polynomial.natDegree_neg, Polynomial.natDegree_mul aNonzero answerZero,
        leftDegree] at rightDegree
      omega
    have equality := Polynomial.resultant_add_mul_right a b answer m n
      productBound leftDegree.le
    rw [add_comm b, identity, Polynomial.resultant_zero_right] at equality
    simpa only [zero_pow positive.ne', zero_mul] using equality.symm

theorem identity_certificate_zero (A B : Polynomial K[X]) (positive : 0 < A.natDegree)
    (t : K) (answer : K[X])
    (identity : atPoint A t * answer + atPoint B t = 0) :
    (certificate A B).eval t = 0 := by
  by_cases leadingZero : A.leadingCoeff.eval t = 0
  · simp only [certificate, Polynomial.eval_mul, leadingZero, zero_mul]
  · have degreePreserved : (atPoint A t).natDegree = A.natDegree := by
      exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl leadingZero)
    have resultantZero := identity_resultant_zero (atPoint A t) (atPoint B t)
      answer A.natDegree B.natDegree positive degreePreserved
      (Polynomial.natDegree_map_le) identity
    have specialized : (Polynomial.resultant A B).eval t = 0 := by
      simpa only [atPoint, Polynomial.resultant_map_map,
        Polynomial.coe_evalRingHom] using resultantZero
    simp only [certificate, Polynomial.eval_mul, specialized, mul_zero]

theorem certificate_degree (A B : Polynomial K[X]) (H : Nat)
    (aBound : ∀ j, (A.coeff j).natDegree ≤ H)
    (bBound : ∀ j, (B.coeff j).natDegree ≤ H) :
    (certificate A B).natDegree ≤ (A.natDegree+B.natDegree+1)*H := by
  have leadingBound : A.leadingCoeff.natDegree ≤ H := aBound A.natDegree
  have resultantBound := resultant_natDegree_le_of_coeff_natDegree_le
    A B A.natDegree B.natDegree H aBound bBound
  calc
    (certificate A B).natDegree ≤ A.leadingCoeff.natDegree +
        (Polynomial.resultant A B).natDegree := Polynomial.natDegree_mul_le
    _ ≤ H + (A.natDegree+B.natDegree)*H := Nat.add_le_add leadingBound resultantBound
    _ = (A.natDegree+B.natDegree+1)*H := by ring

#print axioms certificate_ne_zero
#print axioms identity_resultant_zero
#print axioms identity_certificate_zero
#print axioms certificate_degree
end
end AspisV8.LinearDenominatorOOD
