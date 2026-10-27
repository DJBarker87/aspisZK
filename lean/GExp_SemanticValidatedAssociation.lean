import GExp_SampleBlockAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock

theorem semanticValidated_associated {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (semanticValidated D self record1) := by
  unfold semanticValidated
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply sampleBlock_associated; exact law)
    | (association_then_for sampleBlock
       <;> first | (solve | apply sampleBlock_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms semanticValidated_associated
end AspisR1PublicPreparation.S1SemanticCode
