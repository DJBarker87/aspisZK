import GSWideExactAgreementInputs
import InitialForwardEncoderBaseV9
import RRFinalMessageRecovery

set_option autoImplicit false

namespace AspisWide.GSActualEncoderGRSBridge

open CompPoly CompPoly.GuruswamiSudan
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisWide.InitialForwardEncoderBaseV9
open AspisWideTower
open AspisR1.RRFinalMessageRecovery
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisCircleTensorBinding

variable [BEq WideExact] [LawfulBEq WideExact] [DecidableEq WideExact]
  [NeZero (2 : WideExact)] [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]

theorem initial_normalizedPoints_eq_maintained
    (received : InitialWord WideExact) :
    initialNormalizedPoints received = Array.ofFn (initialWideNormalizedPair received) := by
  rfl

theorem final_normalizedPoints_eq_maintained
    (received : FinalWord WideExact) :
    finalNormalizedPoints received = Array.ofFn (finalWideNormalizedPair received) := by
  rfl

theorem initial_encode_to_grs_messagePolynomial (m : InitialMessage WideExact) :
    (encodeInitialC m).toPoly = initialConversion.messagePolynomial m := by
  rw [encodeInitialC_toPoly]
  change circleNumerator (initialP0 m) (initialP1 m) =
    AspisWide.GRSConversion.exactCircleGRSPolynomial m
  exact (AspisWide.GRSConversion.exactCircleGRSPolynomial_eq_released m).symm

theorem final_encode_to_grs_messagePolynomial (m : FinalMessage WideExact) :
    (encodeFinal m).toPoly = finalConversion.messagePolynomial m := by
  rw [encodeFinal_toPoly]
  simp only [AspisWide.WideExactGRSInstantiation.finalConversion,
    AspisWide.GRSConversion.exactFinalGRSConversion]

theorem initial_encode_degree_lt (m : InitialMessage WideExact) :
    (encodeInitialC m).toPoly.natDegree < 1025 := by
  rw [initial_encode_to_grs_messagePolynomial]
  exact Nat.lt_succ_of_le (initialConversion.messagePolynomial_degree_le m)

theorem final_encode_degree_lt (m : FinalMessage WideExact) :
    (encodeFinal m).toPoly.natDegree < 256 := by
  rw [final_encode_to_grs_messagePolynomial]
  have hbound := finalConversion.messagePolynomial_degree_le m
  have hbound255 : (finalConversion.messagePolynomial m).natDegree ≤ 255 := by
    simpa using hbound
  exact Nat.lt_succ_of_le hbound255


theorem initial_encode_degreeLt (m : InitialMessage WideExact) :
    degreeLt (encodeInitialC m) 1025 := by
  unfold degreeLt
  rw [CPolynomial.degree_toPoly]
  exact (Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (initial_encode_degree_lt m)))

theorem final_encode_degreeLt (m : FinalMessage WideExact) :
    degreeLt (encodeFinal m) 256 := by
  unfold degreeLt
  rw [CPolynomial.degree_toPoly]
  exact (Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (final_encode_degree_lt m)))

#print axioms initial_normalizedPoints_eq_maintained
#print axioms final_normalizedPoints_eq_maintained
#print axioms initial_encode_to_grs_messagePolynomial
#print axioms final_encode_to_grs_messagePolynomial
#print axioms initial_encode_degree_lt
#print axioms final_encode_degree_lt
#print axioms initial_encode_degreeLt
#print axioms final_encode_degreeLt

end AspisWide.GSActualEncoderGRSBridge
