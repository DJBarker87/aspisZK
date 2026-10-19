import GSRuntimeInitialDistanceEncoderBridge
import GSRuntimeFinalDistanceEncoderBridge

set_option autoImplicit false
namespace AspisWide.GSConcreteReceivedWordPoints

open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation

/-- Build actual array entries without evaluating a noncomputable GRS record. -/
def initialPoints (received : InitialWord WideExact) : Array (WideExact × WideExact) :=
  Array.ofFn fun i =>
    (initialRuntimePoint i, (1 + initialRuntimePoint i ^ 2) ^ 512 * received i)

def finalPoints (received : FinalWord WideExact) : Array (WideExact × WideExact) :=
  Array.ofFn fun i => (finalRuntimePoint i, received i)

theorem initialPoints_size (received : InitialWord WideExact) :
    (initialPoints received).size = 1048576 := by
  simp only [initialPoints, Array.size_ofFn]

theorem finalPoints_size (received : FinalWord WideExact) :
    (finalPoints received).size = 262144 := by
  simp only [finalPoints, Array.size_ofFn]

attribute [local irreducible] initialRuntimePoint finalRuntimePoint

theorem initialPoints_eq_normalized (received : InitialWord WideExact) :
    initialPoints received = initialNormalizedPoints received := by
  simp only [initialPoints, initialNormalizedPoints,
    AspisWide.GSNormalizedPointAgreement.normalizedPoints]
  apply congrArg (fun f : Fin 1048576 → WideExact × WideExact => Array.ofFn f)
  funext i
  apply Prod.ext
  · exact initialRuntimePoint_eq_conversion i
  · change (1 + initialRuntimePoint i ^ 2) ^ 512 * received i =
      (initialConversion.multipliers i)⁻¹ * received i
    have hm : (initialConversion.multipliers i)⁻¹ =
        (1 + initialRuntimePoint i ^ 2) ^ 512 := by
      simp only [initialConversion, AspisWide.GRSConversion.exactInitialGRSConversion,
        AspisWide.GRSConversion.exactCircleGRSMultiplier, inv_inv,
        initialRuntimePoint_eq_conversion]
    rw [hm]

theorem finalPoints_eq_normalized (received : FinalWord WideExact) :
    finalPoints received = finalNormalizedPoints received := by
  simp only [finalPoints, finalNormalizedPoints,
    AspisWide.GSNormalizedPointAgreement.normalizedPoints]
  apply congrArg (fun f : Fin 262144 → WideExact × WideExact => Array.ofFn f)
  funext i
  apply Prod.ext
  · exact finalRuntimePoint_eq_conversion i
  · change received i = (finalConversion.multipliers i)⁻¹ * received i
    simp only [finalConversion, AspisWide.GRSConversion.exactFinalGRSConversion,
      inv_one, one_mul]

#print axioms initialPoints
#print axioms finalPoints
#print axioms initialPoints_size
#print axioms finalPoints_size
#print axioms initialPoints_eq_normalized
#print axioms finalPoints_eq_normalized

end AspisWide.GSConcreteReceivedWordPoints
