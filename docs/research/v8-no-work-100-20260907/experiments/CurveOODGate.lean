import AspisFormal.K1.V7ExactCorrelatedAgreementInterpolation

/-! A new use of the pre-OOD trivariate interpolant. Its weighted gamma
degree also bounds substitution of an entire scalar-power OOD answer row.
Candidates may be selected after gamma (or after later challenges): the
bound covers their existential union, not one retrospectively fixed target.
The complementary symbolic-identity branch is retained, NOT called recovery.
No component membership, received polynomiality or decoder success is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000
namespace AspisV8.CurveOODGate
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7Tag73ExactMultiplicityThreeGS
noncomputable section
variable {K : Type*} [Field K]
  {maximumDegree curveDegree weightedDegree ell zBound : Nat}

/-- The same scalar-power answer polynomial as the interpolation machinery.
The caller supplies normalized GRS answers, not raw circle evaluations. -/
def answerCurve (answers : Fin (curveDegree+1) → K) : K[X] :=
  receivedCurvePolynomial (fun lane (_ : Fin 1) => answers lane) 0

theorem answerCurve_degree (answers : Fin (curveDegree+1) → K) :
    (answerCurve answers).natDegree≤curveDegree :=
  receivedCurvePolynomial_natDegree_le (fun lane (_ : Fin 1) => answers lane) 0

/-- P(x,A(gamma),gamma). This is the zero-order Hasse row, with no
constraint asserted at the new OOD point. The received-word kernel and its
nonzero existence are supplied by the previously checked V7 interpolation. -/
def atPoint
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) : K[X] :=
  curveConstraintPolynomial (fun _ : Fin 1 => x)
    (fun lane (_ : Fin 1) => answers lane) coefficients 0 0

theorem atPoint_degree (positive : 0<zBound)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) :
    (atPoint coefficients x answers).natDegree<zBound :=
  curveConstraintPolynomial_natDegree_lt positive (fun _ : Fin 1 => x)
    (fun lane (_ : Fin 1) => answers lane) coefficients 0 0

theorem atPoint_eval (lastRow : maximumDegree*ell≤weightedDegree)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) (gamma : K) :
    (atPoint coefficients x answers).eval gamma=
      interpolationConstraint x ((answerCurve answers).eval gamma) 0
        (specializeCurveCoefficients lastRow coefficients gamma) := by
  exact (interpolationConstraint_specializeCurveCoefficients lastRow
    (fun _ : Fin 1 => x) (fun lane (_ : Fin 1) => answers lane)
    coefficients 0 0 gamma).symm

/-- The polynomial candidate is an arbitrary witness at the actual gamma.
It need not be part of any pre-gamma component family. -/
theorem atPoint_zero_of_candidate (lastRow : maximumDegree*ell≤weightedDegree)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (x : K) (answers : Fin (curveDegree+1) → K) (gamma : K)
    (candidate : K[X])
    (root : interpolationSubstitute
      (specializeCurveCoefficients lastRow coefficients gamma) candidate=0)
    (point : candidate.eval x=(answerCurve answers).eval gamma) :
    (atPoint coefficients x answers).eval gamma=0 := by
  rw [atPoint_eval lastRow,←point,←interpolationSubstitute_eval,root]
  exact Polynomial.eval_zero

/-- Both OOD answer rows and points are fixed before gamma; row1 may have
depended on the earlier OOD point/answer. At each gamma the existential
candidate may be completely different, including a post-alpha selection. -/
def compatible (lastRow : maximumDegree*ell≤weightedDegree)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (points : Fin 2 → K) (answers : Fin 2 → Fin (curveDegree+1) → K)
    (gamma : K) : Prop :=
  ∃ candidate : K[X],
    interpolationSubstitute (specializeCurveCoefficients lastRow coefficients gamma)
      candidate=0 ∧
    ∀ r, candidate.eval (points r)=(answerCurve (answers r)).eval gamma

/-- No union over candidate polynomials or over the two rows. If either
fixed answer polynomial is nonzero, every compatible gamma is one of its
roots. The identity/identity alternative remains an explicit obligation. -/
theorem compatible_card_le (lastRow : maximumDegree*ell≤weightedDegree)
    (positive : 0<zBound)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (points : Fin 2 → K) (answers : Fin 2 → Fin (curveDegree+1) → K)
    (S : Finset K)
    (nonidentity : ∃ r, atPoint coefficients (points r) (answers r)≠0)
    (covered : ∀ gamma∈S, compatible lastRow coefficients points answers gamma) :
    S.card≤zBound-1 := by
  classical
  obtain ⟨r,nonzero⟩ := nonidentity
  have subset : S.val⊆(atPoint coefficients (points r) (answers r)).roots := by
    intro gamma member
    obtain ⟨candidate,root,point⟩ := covered gamma member
    apply (Polynomial.mem_roots nonzero).mpr
    exact atPoint_zero_of_candidate lastRow coefficients (points r) (answers r)
      gamma candidate root (point r)
  have count := Polynomial.card_le_degree_of_subset_roots subset
  have degree := atPoint_degree positive coefficients (points r) (answers r)
  omega

theorem compatible_probability_le (lastRow : maximumDegree*ell≤weightedDegree)
    (positive : 0<zBound)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (points : Fin 2 → K) (answers : Fin 2 → Fin (curveDegree+1) → K)
    (G S : Finset K)
    (nonidentity : ∃ r, atPoint coefficients (points r) (answers r)≠0)
    (covered : ∀ gamma∈S, compatible lastRow coefficients points answers gamma) :
    (S.card:ℚ)/G.card≤(zBound-1:Nat)/(G.card:ℚ) := by
  have cap := compatible_card_le lastRow positive coefficients points answers S
    nonidentity covered
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr cap) (Nat.cast_nonneg _)

#print axioms answerCurve_degree
#print axioms atPoint_degree
#print axioms atPoint_eval
#print axioms atPoint_zero_of_candidate
#print axioms compatible_card_le
#print axioms compatible_probability_le
end
end AspisV8.CurveOODGate
