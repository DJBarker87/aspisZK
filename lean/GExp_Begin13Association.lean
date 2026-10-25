import GExp_SemanticValidatedAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock semanticValidated

theorem begin13_associated {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (begin13 D prefix1 transcript13 val val1 val2 val12 index_mut_back9) := by
  unfold begin13
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply semanticValidated_associated; exact law)
    | (association_then_for semanticValidated
       <;> first | (solve | apply semanticValidated_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms begin13_associated
end AspisR1PublicPreparation.S1SemanticCode
