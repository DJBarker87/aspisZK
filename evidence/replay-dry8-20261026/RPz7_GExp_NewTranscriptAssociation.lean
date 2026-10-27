import RPz7_GExp_BeginAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock semanticValidated begin13 begin9 begin5 begin

theorem newTranscript_associated {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (newTranscript D hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms newTranscript_associated
end AspisR1PublicPreparation.S1SemanticCode
