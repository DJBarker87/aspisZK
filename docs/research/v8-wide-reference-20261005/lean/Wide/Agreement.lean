import Wide.EncoderLinearity
import Wide.Interpolation
import AspisFormal.V6PublishedTheoremInterfaces

/-!
# Exact V7 correlated agreement

This module closes the coding-theory correlated-agreement boundary for the
two exact released V7 encoders.  The released initial code is handled as its
actual 1024-dimensional linear subcode of the ambient maximum-degree-1024
GRS code; it is never enlarged to the full ambient polynomial space.
-/

set_option autoImplicit false

namespace AspisWide.Agreement

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]


open scoped BigOperators
open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisWide.FinalEncoder
open AspisWide.GRSConversion
open AspisWide.MultiplicityThreeGS
open AspisWide.Interpolation
open AspisCircleGroupOrder (P)
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV6Width29CorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-! ## Exact symbolic curve interpolants -/

/-- Divide every initial received lane by the exact nonzero GRS column
multiplier.  This is the lane-wise form of `exactInitialNormalizedReceived`;
it keeps the trivariate interpolation problem in ordinary polynomial-
evaluation coordinates. -/
def exactInitialNormalizedLanes
    (lanes : Fin 29 → InitialWord E) :
    Fin 29 → Fin 1048576 → E := fun lane index =>
  ((exactInitialGRSConversion (K := E)).multipliers index)⁻¹ * lanes lane index

@[simp] theorem exactInitialNormalizedLanes_curve
    (lanes : Fin 29 → InitialWord E) (gamma : E)
    (index : Fin 1048576) :
    (receivedCurvePolynomial (exactInitialNormalizedLanes lanes) index).eval
        gamma =
      exactInitialNormalizedReceived
        (fun coordinate => width29CurveValue lanes gamma coordinate) index := by
  simp only [receivedCurvePolynomial_eval, exactInitialNormalizedLanes,
    exactInitialNormalizedReceived, width29CurveValue, width29Batch]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lane _
  ring

@[simp] theorem exactFinalLanes_curve
    (lanes : Fin 4 → FinalWord E) (z : E)
    (index : Fin 262144) :
    (receivedCurvePolynomial lanes index).eval z =
      curveValue lanes z index := by
  rw [receivedCurvePolynomial_eval, Fin.sum_univ_four]
  simp only [curveValue,
    AspisV5FunctionalBatching.batchedDiscrepancy]
  norm_num

/-- The exact initial width-29 family has a nonzero symbolic
multiplicity-three interpolant.  Candidate messages have not been fixed here:
the six Hasse constraints hold identically in the challenge variable. -/
theorem exists_exactInitialCurveInterpolation
    (lanes : Fin 29 → InitialWord E) :
    ∃ coefficients :
        CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
          initialCurveZBound → E,
      coefficients ≠ 0 ∧
        curveInterpolationMap (exactInitialGRSConversion (K := E)).points
          (exactInitialNormalizedLanes lanes) coefficients = 0 := by
  apply exists_nonzero_curveInterpolationKernel
  exact exactInitialCurveInterpolationBudget.2.2

/-- The exact final degree-three family has a nonzero symbolic
multiplicity-three interpolant over the released `2^18` line domain. -/
theorem exists_exactFinalCurveInterpolation
    (lanes : Fin 4 → FinalWord E) :
    ∃ coefficients :
        CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
          finalCurveZBound → E,
      coefficients ≠ 0 ∧
        curveInterpolationMap (exactFinalGRSConversion (K := E)).points lanes
          coefficients = 0 := by
  apply exists_nonzero_curveInterpolationKernel
  exact exactFinalCurveInterpolationBudget.2.2

/-! ## Every challenge-dependent close candidate is a specialized root -/

-- Large dependent `Fin` indices make elaboration of the exact specialization
-- substantially more expensive than the underlying symbolic proof.
set_option maxHeartbeats 1000000 in
/- A final candidate selected independently at challenge `z` is a root of
the one symbolic interpolant specialized at `z`.  The proof uses only that
challenge's support; no candidate is fixed before `z`. -/
theorem exactFinalValidCandidate_substitute_eq_zero
    (lanes : Fin 4 → FinalWord E)
    (strategy : ProximateStrategy E (Fin 262144)
      (FinalMessage E))
    (coefficients :
      CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
        finalCurveZBound → E)
    (kernel : curveInterpolationMap (exactFinalGRSConversion (K := E)).points lanes
      coefficients = 0)
    (z : E)
    (valid : ValidResponse exactFinalEncoder 9557 lanes strategy z) :
    interpolationSubstitute
        (specializeCurveCoefficients (by norm_num [finalCurveXBound,
          finalCurveYRows]) coefficients z)
        ((exactFinalGRSConversion (K := E)).messagePolynomial
          (strategy.candidate z)) = 0 := by
  let specialized := specializeCurveCoefficients (by
    norm_num [finalCurveXBound, finalCurveYRows]) coefficients z
  have specializedKernel :
      interpolationMap (exactFinalGRSConversion (K := E)).points
        (fun index => curveValue lanes z index) specialized = 0 := by
    have symbolic := specializeCurveCoefficients_mem_kernel
      (by norm_num [finalCurveZBound])
      (by norm_num [finalCurveXBound, finalCurveYRows])
      (exactFinalGRSConversion (K := E)).points lanes coefficients kernel z
    simpa only [exactFinalLanes_curve] using symbolic
  apply interpolationSubstitute_eq_zero_of_agreement (threshold := 9558)
    (exactFinalGRSConversion (K := E)).points (fun index => curveValue lanes z index)
    (exactFinalGRSConversion (K := E)).points_injective specialized specializedKernel
    (by norm_num [finalCurveXBound, finalCurveYRows])
    (by norm_num [finalCurveXBound])
    ((exactFinalGRSConversion (K := E)).messagePolynomial (strategy.candidate z))
    ((exactFinalGRSConversion (K := E)).messagePolynomial_degree_le
      (strategy.candidate z))
  have supportSubset : strategy.support z ⊆
      polynomialAgreementSet (exactFinalGRSConversion (K := E)).points
        (fun index => curveValue lanes z index)
        ((exactFinalGRSConversion (K := E)).messagePolynomial
          (strategy.candidate z)) := by
    intro index indexMem
    rw [mem_polynomialAgreementSet]
    have response := valid.2 index indexMem
    have encoded := congrFun
      (exactFinalEncoder_eq_grs (strategy.candidate z)) index
    unfold ExactGRSConversion.grsEncoder generalizedReedSolomonEncode at encoded
    simpa only [exactFinalGRSConversion, one_mul] using
      encoded.symm.trans response.symm
  have supportCard := Finset.card_le_card supportSubset
  have threshold := valid.1
  omega

-- The width-29 dependent interpolation index requires the same elaboration
-- allowance as the exact final specialization above.
set_option maxHeartbeats 1000000 in
/- The analogous exact statement for the initial width-29 circle code.
The received curve is divided by the proved nonzero GRS multiplier, while the
candidate remains an actual released `Fin 1024 → E` message. -/
theorem exactInitialValidCandidate_substitute_eq_zero
    (lanes : Fin 29 → InitialWord E)
    (strategy : Width29ProximateStrategy E (Fin 1048576)
      (InitialMessage E))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → E)
    (kernel : curveInterpolationMap (exactInitialGRSConversion (K := E)).points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (gamma : E)
    (valid : Width29ValidResponse exactInitialEncoder 38229 lanes strategy
      gamma) :
    interpolationSubstitute
        (specializeCurveCoefficients (by norm_num [initialCurveXBound,
          initialCurveYRows]) coefficients gamma)
        ((exactInitialGRSConversion (K := E)).messagePolynomial
          (strategy.candidate gamma)) = 0 := by
  let specialized := specializeCurveCoefficients (by
    norm_num [initialCurveXBound, initialCurveYRows]) coefficients gamma
  have specializedKernel :
      interpolationMap (exactInitialGRSConversion (K := E)).points
        (exactInitialNormalizedReceived
          (fun index => width29CurveValue lanes gamma index))
        specialized = 0 := by
    have symbolic := specializeCurveCoefficients_mem_kernel
      (by norm_num [initialCurveZBound])
      (by norm_num [initialCurveXBound, initialCurveYRows])
      (exactInitialGRSConversion (K := E)).points (exactInitialNormalizedLanes lanes)
      coefficients kernel gamma
    simpa only [exactInitialNormalizedLanes_curve] using symbolic
  apply interpolationSubstitute_eq_zero_of_agreement (threshold := 38230)
    (exactInitialGRSConversion (K := E)).points
    (exactInitialNormalizedReceived
      (fun index => width29CurveValue lanes gamma index))
    (exactInitialGRSConversion (K := E)).points_injective specialized specializedKernel
    (by norm_num [initialCurveXBound, initialCurveYRows])
    (by norm_num [initialCurveXBound])
    ((exactInitialGRSConversion (K := E)).messagePolynomial (strategy.candidate gamma))
    ((exactInitialGRSConversion (K := E)).messagePolynomial_degree_le
      (strategy.candidate gamma))
  have supportSubset : strategy.support gamma ⊆
      polynomialAgreementSet (exactInitialGRSConversion (K := E)).points
        (exactInitialNormalizedReceived
          (fun index => width29CurveValue lanes gamma index))
        ((exactInitialGRSConversion (K := E)).messagePolynomial
          (strategy.candidate gamma)) := by
    intro index indexMem
    rw [mem_polynomialAgreementSet]
    have response := valid.2 index indexMem
    rw [exactInitialNormalizedReceived, response,
      exactInitialEncoder_coordinate_grs]
    unfold generalizedReedSolomonEncode
    have multiplierNeZero :=
      (exactInitialGRSConversion (K := E)).multipliers_ne_zero index
    field_simp
    simp only [exactInitialGRSConversion]
    ring
  have supportCard := Finset.card_le_card supportSubset
  have threshold := valid.1
  omega

/-! The curve-decodability reconstruction and exact V7 instantiations follow
after the released-code closure layer above. -/

#print axioms exactInitialEncoder_add
#print axioms exactInitialEncoder_smul
#print axioms exactFinalEncoder_add
#print axioms exactFinalEncoder_smul
#print axioms exists_exactInitialCurveInterpolation
#print axioms exists_exactFinalCurveInterpolation
#print axioms exactFinalValidCandidate_substitute_eq_zero
#print axioms exactInitialValidCandidate_substitute_eq_zero

end

end AspisWide.Agreement
