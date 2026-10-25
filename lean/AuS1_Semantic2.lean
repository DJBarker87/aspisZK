import AuS1_Semantic1
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Semantic
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.S1SemanticCode AuS1_Association
theorem newTranscript_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) :
    Uniform hashv (newTranscript D hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem publicTranscript_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    Uniform hashv (publicTranscript D pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | with_reducible apply newTranscript_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem roundStep_uniform (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    Uniform hashv (roundStep B D prefix1 transcript alpha running round) := by
  unfold roundStep
  repeat' first
    | (solve | with_reducible apply semanticValidated_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem rounds_uniform (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    Uniform hashv (rounds B D prefix1 transcript) := by
  unfold rounds
  repeat' first
    | (solve | with_reducible apply roundStep_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

#print axioms newTranscript_uniform
#print axioms publicTranscript_uniform
#print axioms roundStep_uniform
#print axioms rounds_uniform
end AspisR1.AuS1_Semantic
end
