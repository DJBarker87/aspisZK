import RPz7_GExp_FinishAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock semanticValidated begin13 begin9 begin5 begin newTranscript publicTranscript roundStep rounds circleValidated finish

theorem verify_associated (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (verify (finish R B) D pub bytes hash obs) := by
  unfold verify
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply publicTranscript_associated; exact law)
    | (association_then_for publicTranscript
       <;> first | (solve | apply publicTranscript_associated; exact law) | intro x)
    | (solve | apply begin_associated; exact law)
    | (association_then_for begin
       <;> first | (solve | apply begin_associated; exact law) | intro x)
    | (solve | apply finish_associated; exact law)
    | (association_then_for finish
       <;> first | (solve | apply finish_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms verify_associated
end AspisR1PublicPreparation.S1SemanticCode
