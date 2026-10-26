import F3V_EvidenceCalls
import F3V_Decoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldSizes
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem sizes {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) :
    (bytesOf e.pub.val).length=1880 ∧ (bytesOf e.proof.val).length=57607 := by
  obtain ⟨statement,decoded,valid,selected⟩ := F3V_Decoded.fields (sdk c) e.pub e.semantic e.decoded
  have source : AspisS6CurrentCodecInstallation.decode e.pub=ok (.Ok statement) := decoded
  obtain ⟨encoded,returned,contents⟩ := AspisS6CurrentCodecInstallation.accepted_inverse e.pub statement source
  constructor
  · simp only [bytesOf,List.length_map]
    rw [←contents]
    exact encoded.property
  · simpa only [bytesOf,List.length_map] using F3V_EvidenceCalls.length c B s H e

#print axioms sizes
end AspisR1.PFin_WorldSizes
end
