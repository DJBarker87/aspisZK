import GSConcreteReceivedWordPoints
import GSFixedInputDecoderFamily

set_option autoImplicit false
namespace AspisWide.GSConcreteReceivedWordInputs
open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSConcreteReceivedWordPoints
open AspisWide.GSWideExactAgreementInputs
open AspisR1.GSFixedInputDecoderFamily

def fromWords {finalCount : Nat}
    (W : Fin 29 → InitialWord WideExact)
    (V : Fin finalCount → FinalWord WideExact) : Inputs WideExact finalCount where
  initialPoints := fun i => initialPoints (W i)
  initialSize := fun i => initialPoints_size (W i)
  finalPoints := fun i => finalPoints (V i)
  finalSize := fun i => finalPoints_size (V i)

attribute [local irreducible] GSConcreteReceivedWordPoints.initialPoints
  GSConcreteReceivedWordPoints.finalPoints initialNormalizedPoints finalNormalizedPoints

theorem initialPoints_normalized {finalCount : Nat}
    (W : Fin 29 → InitialWord WideExact)
    (V : Fin finalCount → FinalWord WideExact) (i : Fin 29) :
    (fromWords W V).initialPoints i = initialNormalizedPoints (W i) := by
  simpa only [fromWords] using initialPoints_eq_normalized (W i)

theorem finalPoints_normalized {finalCount : Nat}
    (W : Fin 29 → InitialWord WideExact)
    (V : Fin finalCount → FinalWord WideExact) (i : Fin finalCount) :
    (fromWords W V).finalPoints i = finalNormalizedPoints (V i) := by
  simpa only [fromWords] using finalPoints_eq_normalized (V i)

#print axioms fromWords
#print axioms initialPoints_normalized
#print axioms finalPoints_normalized
end AspisWide.GSConcreteReceivedWordInputs
