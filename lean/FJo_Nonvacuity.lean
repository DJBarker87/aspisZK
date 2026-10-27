import FJo_OpeningDecodes
import FJl_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Nonvacuity
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- All 12 retained backend calls inhabit the new strict C1/C2 decode result.
This is local fixture evidence, not joint headline-premise inhabitation. -/
theorem decoded (i : Fin 12) :
    (∃ c1,MixedLeafDecoder.decodeC1
      ((bytesOf (JFo_Opening.value (JFn_Values.position i)).val).take 480)=some c1) ∧
    (∃ c2,MixedLeafDecoder.decodeC2
      (((bytesOf (JFo_Opening.value (JFn_Values.position i)).val).drop 480).take 128)=some c2) := by
  obtain ⟨native,called,same⟩ := FIp_DotsAdapter.reached _ _ _ (JFs_TX2_Dots.adapter i)
  exact FJo_OpeningDecodes.value _ _ native called
#print axioms decoded
#print axioms FJl_Nonvacuity.scalar
end AspisR1.FJo_Nonvacuity
end
