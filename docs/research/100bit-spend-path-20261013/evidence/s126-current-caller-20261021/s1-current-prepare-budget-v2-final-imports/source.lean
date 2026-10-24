import S1SemanticBudgetV1
import S1PreparedBudgetV1
import S1CurrentPrepareCodeExactV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1PrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode PreparedBudget
open AspisS1ValuesOwnedInstallation

theorem closed_bounded {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    bounded 33 (BorrowedClaimPrepared.closedPreparationCode D sem v hash scratch) := by
  unfold BorrowedClaimPrepared.closedPreparationCode
  budget_then 33
  · omega
  · exact preparation_bounded _ _ _ _ _ _ _
  · intro result
    cases result
    exact pure_bound _ _

theorem semantic_bounded (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    bounded 82 (S1SemanticCodeInstallation.code R B D pub bytes hash) := by
  unfold S1SemanticCodeInstallation.code
  budget_then 82
  · omega
  · exact S1SemanticCode.verify_bounded _ _ _ _ _ _ _
  · intro result
    exact pure_bound _ _

attribute [local irreducible] S1SemanticCodeInstallation.code BorrowedClaimPrepared.closedPreparationCode
/-- Every oracle-driven path through the complete source-model prepare body.
No acceptance, canonicality, child success, OracleValid or read-count premise. -/
theorem prepare_bounded (base : Ops) (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    bounded 115 (prepare base R B D pub proof hash scratch) := by
  unfold prepare
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=82) <;> first | omega | (solve | apply semantic_bounded))
    | (apply mono (n:=33) <;> first | omega | (solve | apply closed_bounded))
    | (budget_then_for 82 S1SemanticCodeInstallation.code
       <;> first | omega | (solve | apply semantic_bounded) | intro x)
    | (budget_then_for 33 BorrowedClaimPrepared.closedPreparationCode
       <;> first | omega | (solve | apply closed_bounded) | intro x)
    | (apply lift_bind;intro x)
    | split

#print axioms closed_bounded
#print axioms semantic_bounded
#print axioms prepare_bounded
end AspisR1CurrentCaller.S1PrepareCode
