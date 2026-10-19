import GSRuntimeInitialDistanceEncoderBridge
import GSRuntimeInitialJointKeepCore
import R1InitialResponses
import R1ConcreteBinding

set_option autoImplicit false

namespace AspisWide.GSConcreteInitialRuntimeJointCandidates

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWideTower

/-- Run the checked per-lane runtime close-list outputs through the executable
joint-list merge in canonical lane order. -/
def jointCandidates (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact)) :
    List (Fin 29 → InitialMessage WideExact) :=
  AspisWide.GSRuntimeInitialJointKeepCore.runtimeCandidates
    AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeEncoder
    W decoded (List.finRange 29)

theorem finRange29_covers : (List.finRange 29).toFinset = Finset.univ := by
  ext i
  simp

theorem jointCandidates_length_le_100
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact)) :
    (jointCandidates W decoded).length ≤ 100 := by
  simpa [jointCandidates] using
    AspisWide.GSRuntimeInitialJointKeepCore.runtimeCandidates_length_le_100
      AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeEncoder
      AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeEncoder_eq_released
      W decoded (List.finRange 29)

theorem jointCandidates_to_bindingCandidates
    (W : Fin 29 → InitialWord WideExact)
    (decoded : Fin 29 → List (InitialMessage WideExact))
    (hcomplete : ∀ lane,
      AspisR1.InitialResponses.Close (W lane) ⊆ (decoded lane).toFinset) :
    (jointCandidates W decoded).toFinset = AspisR1.ConcreteBinding.candidates W := by
  unfold jointCandidates
  exact AspisWide.GSRuntimeInitialJointKeepCore.runtimeCandidates_to_bindingCandidates
    AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeEncoder
    AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeEncoder_eq_released
    W decoded (List.finRange 29) finRange29_covers hcomplete

#print axioms jointCandidates
#print axioms finRange29_covers
#print axioms jointCandidates_length_le_100
#print axioms jointCandidates_to_bindingCandidates

end AspisWide.GSConcreteInitialRuntimeJointCandidates
