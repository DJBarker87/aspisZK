import CurveOODGate
import AspisFormal.K1.V7ExactCorrelatedAgreementFactors

/-! The actual first-Y Hasse row of the fixed trivariate interpolant,
evaluated along the degree-28 component-answer curve. Differentiating in Y
removes one complete answer-degree contribution. Nonzeroness is deliberately
NOT inferred from an OOD identity: repeated factors can make this row zero.
The zero-polynomial alternative remains an unbounded classification branch.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000
namespace AspisV8.CurveOODDerivative
open Polynomial Finset
open AspisV8.CurveOODGate
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactMultiplicityThreeGS
noncomputable section
variable {K : Type*} [Field K]
  {maximumDegree curveDegree xBound yRows zBound : Nat}

def atPoint
    (coefficients : CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) : K[X] :=
  curveConstraintPolynomial (fun _ : Fin 1 => x)
    (fun lane (_ : Fin 1) => answers lane) coefficients 0 2

theorem atPoint_sum
    (coefficients : CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) :
    atPoint coefficients x answers = ∑ m,
      C (coefficients m*x^m.2.1.1*(m.1.1:K)) *
        (answerCurve answers^(m.1.1-1)*X^m.2.2.1) := by
  classical
  simp only [atPoint,curveConstraintPolynomial,hasseXOrder_two,hasseYOrder_two,
    Nat.choose_zero_right,Nat.choose_one_right,Nat.cast_one,mul_one,Nat.sub_zero,answerCurve]

theorem atPoint_degree
    (coefficients : CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) :
    (atPoint coefficients x answers).natDegree ≤ zBound-curveDegree-1 := by
  classical
  rw [atPoint_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  by_cases zero : m.1.1=0
  · simp only [zero,Nat.cast_zero,mul_zero,Polynomial.C_0,zero_mul,
      Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · have positive : 1 ≤ m.1.1 := by omega
    have strict : curveDegree*m.1.1+m.2.2.1<zBound := by
      have bound := m.2.2.2
      omega
    have shift := congrArg (fun n : Nat => n*curveDegree)
      (Nat.sub_add_cancel positive)
    simp only [Nat.add_mul,one_mul] at shift
    have degree := answerCurve_degree answers
    calc
      (C (coefficients m*x^m.2.1.1*(m.1.1:K)) *
          (answerCurve answers^(m.1.1-1)*X^m.2.2.1)).natDegree
          ≤ (answerCurve answers^(m.1.1-1)*X^m.2.2.1).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ (answerCurve answers^(m.1.1-1)).natDegree+
          (X^m.2.2.1:K[X]).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (m.1.1-1)*curveDegree+m.2.2.1 :=
        Nat.add_le_add (Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_left _ degree)) (by simp)
      _ ≤ zBound-curveDegree-1 := by
        have commute := Nat.mul_comm curveDegree m.1.1
        omega

theorem interpolationConstraint_two_derivative
    {weightedDegree ell : Nat}
    (coefficients : WeightedMonomialIndex maximumDegree weightedDegree ell → K)
    (x y : K) :
    interpolationConstraint x y 2 coefficients =
      ((weightedBivariatePolynomial coefficients).derivative.map
        (Polynomial.evalRingHom x)).eval y := by
  classical
  simp only [weightedBivariatePolynomial,Polynomial.derivative_sum,
    Polynomial.derivative_monomial,Polynomial.map_sum,Polynomial.map_monomial,
    Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    Polynomial.coe_evalRingHom,map_mul,map_natCast,
    interpolationConstraint_apply,hasseXOrder_two,hasseYOrder_two,
    Nat.choose_zero_right,Nat.choose_one_right,Nat.cast_one,mul_one,Nat.sub_zero]

/-- This is the literal derivative of the same specialized interpolant,
not a fresh auxiliary polynomial unrelated to the adaptive candidate. -/
theorem atPoint_eval
    {weightedDegree ell : Nat} (lastRow : maximumDegree*ell≤weightedDegree)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) (gamma : K) :
    (atPoint coefficients x answers).eval gamma =
      ((specializeChallenge gamma (curveTrivariatePolynomial coefficients)).derivative.map
        (Polynomial.evalRingHom x)).eval ((answerCurve answers).eval gamma) := by
  rw [specializeChallenge_curveTrivariatePolynomial lastRow,
    ←interpolationConstraint_two_derivative]
  exact (interpolationConstraint_specializeCurveCoefficients lastRow
    (fun _ : Fin 1 => x) (fun lane (_ : Fin 1) => answers lane)
    coefficients 0 2 gamma).symm

theorem root_card_le
    (coefficients : CurveMonomialIndex maximumDegree curveDegree xBound yRows zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) (S : Finset K)
    (nonzero : atPoint coefficients x answers≠0)
    (roots : ∀ gamma∈S, (atPoint coefficients x answers).eval gamma=0) :
    S.card≤zBound-curveDegree-1 := by
  classical
  have subset : S.val⊆(atPoint coefficients x answers).roots := by
    intro gamma member
    exact (Polynomial.mem_roots nonzero).mpr (roots gamma member)
  exact (Polynomial.card_le_degree_of_subset_roots subset).trans
    (atPoint_degree coefficients x answers)

theorem selected_degree
    (coefficients : CurveMonomialIndex 1024 28 114688 112 117078 → K)
    (x : K) (answers : Fin 29 → K) :
    (atPoint coefficients x answers).natDegree≤117049 :=
  atPoint_degree coefficients x answers

#print axioms atPoint_sum
#print axioms atPoint_degree
#print axioms interpolationConstraint_two_derivative
#print axioms atPoint_eval
#print axioms root_card_le
#print axioms selected_degree
end
end AspisV8.CurveOODDerivative
