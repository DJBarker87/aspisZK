import RPz7_AuS1_Prepared
import RPz7_AuS1_Semantic3
import RPz7_SdkD_PrepareTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Prepare
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Association
open AspisR1CurrentCaller

 theorem semantic_uniform
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    Uniform hashv (S1SemanticCodeInstallation.code R B D pub bytes hash) := by
  unfold S1SemanticCodeInstallation.code
  apply bind_uniform
  · apply AuS1_Semantic.verify_uniform
    exact law
  · intro x; apply pure_uniform

 theorem original_uniform {H : Type} (D : aspis_core.digest.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H) (v : AspisR1CurrentCaller.verifier.View)
    (hash : H) (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    Uniform hashv (BorrowedClaimPrepared.closedPreparationCode D sem v hash scratch) := by
  unfold BorrowedClaimPrepared.closedPreparationCode
  apply bind_uniform
  · apply AuS1_Prepared.uniform
    exact law
  · intro x; apply pure_uniform

 theorem uniform (ops : Ops) (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    Uniform hashv (SdkD_PrepareSource.code ops B std D pub proof hash scratch) := by
  unfold SdkD_PrepareSource.code S1PrepareCode.prepare
  repeat' first
    | (solve | with_reducible apply semantic_uniform; assumption)
    | (solve | with_reducible apply original_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | with_reducible apply bind_uniform
    | intro x
    | split

 theorem associated (ops : Ops) (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    SdkD_PrepareLower.Associated hashv (SdkD_PrepareSource.code ops B std D pub proof hash scratch) :=
  AuS1_Association.associated hashv _ (uniform ops B std D hashv law pub proof hash scratch)

#print axioms semantic_uniform
#print axioms original_uniform
#print axioms uniform
#print axioms associated
end AspisR1.AuS1_Prepare
end
