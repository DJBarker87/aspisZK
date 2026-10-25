import GExp_Begin5Association
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock semanticValidated begin13 begin9 begin5

theorem begin_associated {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (begin D prefix1 transcript) := by
  unfold begin
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply semanticValidated_associated; exact law)
    | (association_then_for semanticValidated
       <;> first | (solve | apply semanticValidated_associated; exact law) | intro x)
    | (solve | apply begin5_associated; exact law)
    | (association_then_for begin5
       <;> first | (solve | apply begin5_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms begin_associated
end AspisR1PublicPreparation.S1SemanticCode
