import GExp_RoundStepAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock semanticValidated begin13 begin9 begin5 begin newTranscript publicTranscript roundStep

theorem rounds_associated (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (rounds B D prefix1 transcript) := by
  unfold rounds
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply roundStep_associated; exact law)
    | (association_then_for roundStep
       <;> first | (solve | apply roundStep_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms rounds_associated
end AspisR1PublicPreparation.S1SemanticCode
