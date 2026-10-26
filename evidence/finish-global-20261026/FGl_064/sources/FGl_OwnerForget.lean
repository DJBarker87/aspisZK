import FGl_Transport
import F3Y_PreparedAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_OwnerForget
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- The original thirteen global families imply the new twelve at identical
Evidence/At/Calls/primitive witnesses. No acceptance or world is changed. -/
theorem weaken {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : F3Y_PreparedAt.Owners c B) : FGl_PreparedAt.Owners c B := by
  intro s H e i p q data t atPrepared calls x
  have leaves := old s H e i p q data t atPrepared calls x
  exact ⟨⟨leaves.1.round0,leaves.1.round1,leaves.1.pair⟩,
    leaves.2.1,leaves.2.2.1,leaves.2.2.2.1⟩

#print axioms weaken
end AspisR1.FGl_OwnerForget
end
