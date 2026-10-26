import RPz7_AuS1_Association
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Semantic
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.S1SemanticCode AuS1_Association
theorem sampleBlock_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    Uniform hashv (sampleBlock D self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem semanticValidated_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    Uniform hashv (semanticValidated D self record1) := by
  unfold semanticValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem begin13_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    Uniform hashv (begin13 D prefix1 transcript13 val val1 val2 val12 index_mut_back9) := by
  unfold begin13
  repeat' first
    | (solve | with_reducible apply semanticValidated_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem begin9_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
    (val val1 val2 val8 : aspis_core.field.QM31)
    (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    Uniform hashv (begin9 D prefix1 transcript9 val val1 val2 val8 index_mut_back5) := by
  unfold begin9
  repeat' first
    | (solve | with_reducible apply semanticValidated_uniform; assumption)
    | (solve | with_reducible apply begin13_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem begin5_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
    (val val1 val2 val4 : aspis_core.field.QM31)
    (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    Uniform hashv (begin5 D prefix1 transcript5 val val1 val2 val4 index_mut_back1) := by
  unfold begin5
  repeat' first
    | (solve | with_reducible apply semanticValidated_uniform; assumption)
    | (solve | with_reducible apply begin9_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem begin_uniform  {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    Uniform hashv (begin D prefix1 transcript) := by
  unfold begin
  repeat' first
    | (solve | with_reducible apply semanticValidated_uniform; assumption)
    | (solve | with_reducible apply begin5_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

#print axioms sampleBlock_uniform
#print axioms semanticValidated_uniform
#print axioms begin13_uniform
#print axioms begin9_uniform
#print axioms begin5_uniform
#print axioms begin_uniform
end AspisR1.AuS1_Semantic
end
