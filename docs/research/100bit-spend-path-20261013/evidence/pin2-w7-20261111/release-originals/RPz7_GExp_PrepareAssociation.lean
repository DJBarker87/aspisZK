import RPz7_GExp_PreparedPreparationAssociation
import RPz7_SdkD_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_PrepareAssociation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation PreparedHashCode
open GExp_Association

theorem closed {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H) (v : AspisR1CurrentCaller.verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    SdkD_PrepareLower.Associated hashv
      (BorrowedClaimPrepared.closedPreparationCode D sem v hash scratch) := by
  unfold BorrowedClaimPrepared.closedPreparationCode
  association_then
  · apply PreparedBudget.preparation_associated
    exact law
  · intro result
    cases result
    exact pure_associated _ _

theorem semantic (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    SdkD_PrepareLower.Associated hashv (S1SemanticCodeInstallation.code R B D pub bytes hash) := by
  unfold S1SemanticCodeInstallation.code
  association_then
  · apply S1SemanticCode.verify_associated
    exact law
  · intro result
    exact pure_associated _ _

attribute [local irreducible] S1SemanticCodeInstallation.code BorrowedClaimPrepared.closedPreparationCode

theorem prepare (base : Ops) (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    SdkD_PrepareLower.Associated hashv (S1PrepareCode.prepare base R B D pub proof hash scratch) := by
  unfold S1PrepareCode.prepare
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply semantic; exact law)
    | (solve | apply closed; exact law)
    | (association_then_for S1SemanticCodeInstallation.code
       <;> first | (solve | apply semantic; exact law) | intro x)
    | (association_then_for BorrowedClaimPrepared.closedPreparationCode
       <;> first | (solve | apply closed; exact law) | intro x)
    | (apply lift_bind_associated;intro x)
    | split

#print axioms closed
#print axioms semantic
#print axioms prepare
end AspisR1.GExp_PrepareAssociation
end
