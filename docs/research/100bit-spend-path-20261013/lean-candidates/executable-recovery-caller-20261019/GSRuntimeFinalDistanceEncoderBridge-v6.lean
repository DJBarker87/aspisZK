import GSFinalMessageCandidateFilter
import CompPoly.Univariate.ToPoly.Impl
import GSActualEncoderGRSBridge
import GSWideExactAgreementInputs
import RRFinalMessageRecovery
import WideExactGRSInstantiationV5
import AspisFormal.V7ExactOneFoldDomains
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false

namespace AspisWide.GSRuntimeFinalDistanceEncoderBridge

open CompPoly
open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV7ExactOneFoldDomains
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisWide.GSActualEncoderGRSBridge
open AspisWide.GSFinalMessageCandidateFilter
open AspisWideTower
open AspisR1.RRFinalMessageRecovery

variable [DecidableEq WideExact]

/-- Literal stored line point used by the executable final encoder. -/
def finalRuntimePoint (i : Fin 262144) : WideExact :=
  algebraMap (ZMod P) WideExact (storedFirstLineX18 i)

/-- Computable final encoder evaluation over the CPolynomial representation. -/
def finalRuntimeEncoder (m : FinalMessage WideExact) : FinalWord WideExact :=
  fun i => CPolynomial.eval (finalRuntimePoint i) (encodeFinal m)

theorem finalRuntimePoint_eq_conversion (i : Fin 262144) :
    finalRuntimePoint i = finalConversion.points i := by
  rfl

theorem finalRuntimeEncoder_eq_released (m : FinalMessage WideExact) :
    finalRuntimeEncoder m =
      AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) m := by
  funext i
  have hp := finalRuntimePoint_eq_conversion i
  have hm : (1 : WideExact) = finalConversion.multipliers i := by
    simp [finalConversion, AspisWide.GRSConversion.exactFinalGRSConversion]
  have he : CPolynomial.eval (finalRuntimePoint i) (encodeFinal m) =
      (finalConversion.messagePolynomial m).eval (finalConversion.points i) := by
    rw [CPolynomial.eval_toPoly, final_encode_to_grs_messagePolynomial, hp]
  have hc := finalConversion.coordinate_identity m i
  change AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) m i =
      finalConversion.multipliers i *
        (finalConversion.messagePolynomial m).eval (finalConversion.points i) at hc
  dsimp [finalRuntimeEncoder]
  calc
    CPolynomial.eval (finalRuntimePoint i) (encodeFinal m) =
        1 * CPolynomial.eval (finalRuntimePoint i) (encodeFinal m) := by simp
    _ = finalConversion.multipliers i *
        (finalConversion.messagePolynomial m).eval (finalConversion.points i) := by
          rw [hm, he]
    _ = AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) m i := hc.symm

/-- Runtime distance predicate over the literal evaluator. -/
def finalRuntimeCloseAtLeast (received : FinalWord WideExact)
    (m : FinalMessage WideExact) : Prop :=
  9558 ≤ agreementCount received (finalRuntimeEncoder m)

/-- Executable candidate list after image filtering and final distance testing. -/
def finalRuntimeCloseList (received : FinalWord WideExact)
    (candidates : List (List WideExact)) : List (FinalMessage WideExact) :=
  (AspisWide.GSFinalMessageCandidateFilter.filterCandidates candidates).filter
    (fun m => decide (9558 ≤ agreementCount received (finalRuntimeEncoder m)))

theorem finalRuntimeClose_iff_exact (received : FinalWord WideExact)
    (m : FinalMessage WideExact) :
    finalRuntimeCloseAtLeast received m ↔
      closeAtLeast 9558
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact)) received m := by
  simp [finalRuntimeCloseAtLeast, closeAtLeast, agreementCount, finalRuntimeEncoder_eq_released]

theorem finalRuntimeCloseList_mem_iff (received : FinalWord WideExact)
    (candidates : List (List WideExact)) (m : FinalMessage WideExact) :
    m ∈ finalRuntimeCloseList received candidates ↔
      m ∈ AspisWide.GSFinalMessageCandidateFilter.filterCandidates candidates ∧
        closeAtLeast 9558
          (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
          received m := by
  simp [finalRuntimeCloseList, finalRuntimeCloseAtLeast, closeAtLeast,
    agreementCount, finalRuntimeEncoder_eq_released]

#print axioms finalRuntimePoint
#print axioms finalRuntimeEncoder
#print axioms finalRuntimeEncoder_eq_released
#print axioms finalRuntimeCloseList
#print axioms finalRuntimeCloseList_mem_iff

end AspisWide.GSRuntimeFinalDistanceEncoderBridge
