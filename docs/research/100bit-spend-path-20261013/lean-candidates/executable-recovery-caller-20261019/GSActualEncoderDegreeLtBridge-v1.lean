import GSActualEncoderGRSBridge
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness

set_option autoImplicit false

namespace AspisWide.GSActualEncoderDegreeLtBridge

open CompPoly
open CompPoly.GuruswamiSudan
open AspisWide.GSWideExactAgreementInputs
open AspisWide.InitialForwardEncoderBaseV9
open AspisWideTower
open AspisR1.RRFinalMessageRecovery

variable [BEq WideExact] [LawfulBEq WideExact] [DecidableEq WideExact]
  [NeZero (2 : WideExact)] [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]

theorem initial_encode_degreeLt (m : InitialMessage WideExact) :
    degreeLt (encodeInitialC m) 1025 := by
  unfold degreeLt
  rw [CPolynomial.degree_toPoly]
  exact (Polynomial.degree_le_natDegree).trans_lt
    (WithBot.coe_lt_coe.mpr
      (AspisWide.GSActualEncoderGRSBridge.initial_encode_degree_lt m))

theorem final_encode_degreeLt (m : FinalMessage WideExact) :
    degreeLt (encodeFinal m) 256 := by
  unfold degreeLt
  rw [CPolynomial.degree_toPoly]
  exact (Polynomial.degree_le_natDegree).trans_lt
    (WithBot.coe_lt_coe.mpr
      (AspisWide.GSActualEncoderGRSBridge.final_encode_degree_lt m))

#print axioms initial_encode_degreeLt
#print axioms final_encode_degreeLt

end AspisWide.GSActualEncoderDegreeLtBridge
