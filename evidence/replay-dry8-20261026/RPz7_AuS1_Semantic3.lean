import RPz7_AuS1_Semantic2
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Semantic
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.S1SemanticCode AuS1_Association
theorem circleValidated_uniform (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    Uniform hashv (circleValidated B D self record1) := by
  unfold circleValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem finish_uniform (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    Uniform hashv (finish R B D pub prefix1 transcript challenges obs) := by
  unfold finish
  repeat' first
    | (solve | with_reducible apply rounds_uniform; assumption)
    | (solve | with_reducible apply circleValidated_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem verify_uniform (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    Uniform hashv (verify (finish R B) D pub bytes hash obs) := by
  unfold verify
  repeat' first
    | (solve | with_reducible apply publicTranscript_uniform; assumption)
    | (solve | with_reducible apply begin_uniform; assumption)
    | (solve | with_reducible apply finish_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split


#print axioms circleValidated_uniform
#print axioms finish_uniform
#print axioms verify_uniform
end AspisR1.AuS1_Semantic
end
