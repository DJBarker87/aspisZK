import RPz7_AuS1_Semantic3
import RPz7_GExp_VerifyAssociation
import RPz7_S1SemanticBudgetV1
import PIN2_S1SemanticCodeVerifyV1
/-! PIN2 W7 (2026-11-11), option L2: the release uniformity (AuS1_Semantic2/3), association
(GExp_NewTranscript/PublicTranscript/VerifyAssociation) and budget (S1SemanticBudgetV1)
lemmas for the PIN2 lifts `AspisR1PublicPreparationPIN2.S1SemanticCode.{newTranscript,
publicTranscript}` and for `S1SemanticCode.{publicTranscriptPIN2, verifyPIN2}`.  Each proof
is the release tactic script with the PIN2 names; the budget stays 1 / 1 / 82. -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result

/-! Budget. -/
namespace AspisR1PublicPreparationPIN2.S1SemanticCode
open AspisR1PublicPreparationPIN2
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedBudget
attribute [local irreducible] AspisR1PublicPreparation.PreparedHashCode.effects

theorem newTranscript_bounded {H : Type} (D : aspis_core.digest.Digest32 H)
    (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) : bounded 1 (newTranscript D hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] newTranscript

theorem publicTranscript_bounded {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) : bounded 1 (publicTranscript D pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1)
       <;> first | omega | (solve | apply newTranscript_bounded))
    | (budget_then_for 1 newTranscript
       <;> first | omega | (solve | apply newTranscript_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

#print axioms newTranscript_bounded
#print axioms publicTranscript_bounded
end AspisR1PublicPreparationPIN2.S1SemanticCode

namespace AspisR1PublicPreparation.S1SemanticCode
open PreparedHashCode PreparedBudget
attribute [local irreducible] PreparedHashCode.effects AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript
  AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript

theorem publicTranscriptPIN2_bounded {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    bounded 1 (publicTranscriptPIN2 D pub hash root) := by
  unfold publicTranscriptPIN2
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1)
       <;> first | omega | (solve | apply AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript_bounded))
    | (budget_then_for 1 AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript
       <;> first | omega | (solve | apply AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript_bounded) | intro x)
    | (apply lift_bind;intro x)
    | split

attribute [local irreducible] publicTranscriptPIN2 begin finish

theorem verifyPIN2_bounded (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) : bounded 82 (verifyPIN2 (finish R B) D pub bytes hash obs) := by
  unfold verifyPIN2
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1)
       <;> first | omega | (solve | apply publicTranscriptPIN2_bounded))
    | (budget_then_for 1 publicTranscriptPIN2
       <;> first | omega | (solve | apply publicTranscriptPIN2_bounded) | intro x)
    | (apply mono (n:=45)
       <;> first | omega | (solve | apply begin_bounded))
    | (budget_then_for 45 begin
       <;> first | omega | (solve | apply begin_bounded) | intro x)
    | (apply mono (n:=36)
       <;> first | omega | (solve | apply finish_bounded))
    | (budget_then_for 36 finish
       <;> first | omega | (solve | apply finish_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

#print axioms publicTranscriptPIN2_bounded
#print axioms verifyPIN2_bounded
end AspisR1PublicPreparation.S1SemanticCode

/-! Association. -/
namespace AspisR1PublicPreparationPIN2.S1SemanticCode
open AspisR1PublicPreparationPIN2
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] AspisR1PublicPreparation.PreparedHashCode.effects

theorem newTranscript_associated {H : Type} (D : aspis_core.digest.Digest32 H)
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

attribute [local irreducible] newTranscript

theorem publicTranscript_associated {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (publicTranscript D pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply newTranscript_associated; exact law)
    | (association_then_for newTranscript
       <;> first | (solve | apply newTranscript_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms newTranscript_associated
#print axioms publicTranscript_associated
end AspisR1PublicPreparationPIN2.S1SemanticCode

namespace AspisR1PublicPreparation.S1SemanticCode
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects sampleBlock semanticValidated begin13 begin9 begin5 begin newTranscript
  roundStep rounds circleValidated finish
  AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript

theorem publicTranscriptPIN2_associated {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (publicTranscriptPIN2 D pub hash root) := by
  unfold publicTranscriptPIN2
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript_associated; exact law)
    | (association_then_for AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript
       <;> first | (solve | apply AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | split

attribute [local irreducible] publicTranscriptPIN2

theorem verifyPIN2_associated (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (verifyPIN2 (finish R B) D pub bytes hash obs) := by
  unfold verifyPIN2
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply publicTranscriptPIN2_associated; exact law)
    | (association_then_for publicTranscriptPIN2
       <;> first | (solve | apply publicTranscriptPIN2_associated; exact law) | intro x)
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

#print axioms publicTranscriptPIN2_associated
#print axioms verifyPIN2_associated
end AspisR1PublicPreparation.S1SemanticCode

/-! Uniformity. -/
namespace AspisR1.AuS1_Semantic
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.S1SemanticCode AuS1_Association

theorem pin2_newTranscript_uniform {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) :
    Uniform hashv (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash publicBytes root) := by
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript
  repeat' first
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem pin2_publicTranscript_uniform {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    Uniform hashv (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root) := by
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript
  repeat' first
    | (solve | with_reducible apply pin2_newTranscript_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

attribute [local irreducible] AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript in
theorem publicTranscriptPIN2_uniform {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    Uniform hashv (publicTranscriptPIN2 D pub hash root) := by
  unfold publicTranscriptPIN2
  repeat' first
    | (solve | apply pin2_publicTranscript_uniform; exact law)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | with_reducible apply bind_uniform
    | intro x
    | split

theorem verifyPIN2_uniform (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    Uniform hashv (verifyPIN2 (finish R B) D pub bytes hash obs) := by
  unfold verifyPIN2
  repeat' first
    | (solve | with_reducible apply publicTranscriptPIN2_uniform; assumption)
    | (solve | with_reducible apply begin_uniform; assumption)
    | (solve | with_reducible apply finish_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | with_reducible apply bind_uniform
    | intro x
    | split

#print axioms pin2_newTranscript_uniform
#print axioms pin2_publicTranscript_uniform
#print axioms publicTranscriptPIN2_uniform
#print axioms verifyPIN2_uniform
end AspisR1.AuS1_Semantic
end
