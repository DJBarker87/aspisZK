import GSInitialMessageCandidateFilter
import CompPoly.Univariate.ToPoly.Impl
import GSActualEncoderGRSBridge
import GSWideExactAgreementInputs
import RRFinalMessageRecovery
import WideExactGRSInstantiationV5
import AspisFormal.V7ExactOneFoldDomains
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false

namespace AspisWide.GSRuntimeInitialDistanceEncoderBridge

open CompPoly
open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV7ExactOneFoldDomains
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisWide.GSActualEncoderGRSBridge
open AspisWide.InitialForwardEncoderBaseV9
open AspisWide.GSInitialMessageCandidateFilter
open AspisWideTower
open AspisR1.RRFinalMessageRecovery


/-- Literal executable stereographic evaluation point used by the initial
released encoder. This avoids evaluating the noncomputable GRS conversion
record in runtime code. -/
def initialRuntimePoint (i : Fin 1048576) : WideExact :=
  algebraMap (ZMod P) WideExact
    ((AspisV7ExactOneFoldDomains.storedInitialCirclePoint20 i).1.2 /
      (1 + AspisCircleGroupOrder.X (AspisV7ExactOneFoldDomains.storedInitialCirclePoint20 i)))

/-- Evaluate the actual computable initial CPolynomial, with the released
512-power column multiplier expressed directly in field operations. -/
def initialRuntimeEncoder (m : InitialMessage WideExact) : InitialWord WideExact :=
  fun i =>
    ((1 + (initialRuntimePoint i) ^ 2) ^ 512)⁻¹ *
      CPolynomial.eval (initialRuntimePoint i) (encodeInitialC m)

theorem initialRuntimePoint_eq_conversion (i : Fin 1048576) :
    initialRuntimePoint i = initialConversion.points i := by
  change algebraMap (ZMod P) WideExact
      ((AspisV7ExactOneFoldDomains.storedInitialCirclePoint20 i).1.2 /
        (1 + AspisCircleGroupOrder.X
          (AspisV7ExactOneFoldDomains.storedInitialCirclePoint20 i))) =
      AspisWide.GRSConversion.exactCircleGRSPoint i
  rw [AspisWide.GRSConversion.exactCircleGRSPoint_eq_stored]

theorem initialRuntimeEncoder_eq_released (m : InitialMessage WideExact) :
    initialRuntimeEncoder m =
      AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) m := by
  funext i
  have hp := initialRuntimePoint_eq_conversion i
  have hm : ((1 + (initialRuntimePoint i) ^ 2) ^ 512)⁻¹ =
      initialConversion.multipliers i := by
    simp [initialConversion, AspisWide.GRSConversion.exactInitialGRSConversion,
      AspisWide.GRSConversion.exactCircleGRSMultiplier, hp]
  have he : CPolynomial.eval (initialRuntimePoint i) (encodeInitialC m) =
      (initialConversion.messagePolynomial m).eval (initialConversion.points i) := by
    rw [CPolynomial.eval_toPoly,
      AspisWide.GSActualEncoderGRSBridge.initial_encode_to_grs_messagePolynomial,
      hp]
  have hc := initialConversion.coordinate_identity m i
  change AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) m i =
      initialConversion.multipliers i *
        (initialConversion.messagePolynomial m).eval
          (initialConversion.points i) at hc
  dsimp [initialRuntimeEncoder]
  rw [hm, he]
  exact hc.symm

/-- The runtime predicate uses only literal CPolynomial evaluation and finite
agreement counting. -/
def initialRuntimeCloseAtLeast (received : InitialWord WideExact)
    (m : InitialMessage WideExact) : Prop :=
  38230 ≤ agreementCount received (initialRuntimeEncoder m)

/-- Executable distance-filter list preserving the raw candidate order. -/
def initialRuntimeCloseList (received : InitialWord WideExact)
    (candidates : List (List WideExact)) : List (InitialMessage WideExact) :=
  (AspisWide.GSInitialMessageCandidateFilter.filterCandidates candidates).filter
    (fun m => decide (38230 ≤ agreementCount received (initialRuntimeEncoder m)))

theorem initialRuntimeClose_iff_exact (received : InitialWord WideExact)
    (m : InitialMessage WideExact) :
    initialRuntimeCloseAtLeast received m ↔
      closeAtLeast 38230
        (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
        received m := by
  simp [initialRuntimeCloseAtLeast, closeAtLeast, agreementCount,
    initialRuntimeEncoder_eq_released]

theorem initialRuntimeCloseList_mem_iff (received : InitialWord WideExact)
    (candidates : List (List WideExact)) (m : InitialMessage WideExact) :
    m ∈ initialRuntimeCloseList received candidates ↔
      m ∈ AspisWide.GSInitialMessageCandidateFilter.filterCandidates candidates ∧
        closeAtLeast 38230
          (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
          received m := by
  simp [initialRuntimeCloseList, initialRuntimeCloseAtLeast, closeAtLeast,
    agreementCount, initialRuntimeEncoder_eq_released]

#print axioms initialRuntimePoint
#print axioms initialRuntimeEncoder
#print axioms initialRuntimeEncoder_eq_released
#print axioms initialRuntimeCloseList
#print axioms initialRuntimeClose_iff_exact
#print axioms initialRuntimeCloseList_mem_iff

end AspisWide.GSRuntimeInitialDistanceEncoderBridge
