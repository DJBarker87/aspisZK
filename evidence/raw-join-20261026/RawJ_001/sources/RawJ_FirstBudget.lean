import GExq_FirstBudget
import GExq_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_FirstBudget
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect GExp_CountLaws
local instance : MonadLift Result Code where monadLift := liftResult
attribute [local irreducible] SdkD_PrepareLower.lower GExq_BatchSource.current GExp_FirstCode.writerCode

theorem first {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    count 1018 (GExq_FirstCode.code base B std hashv D semantic pub proof split hash) := by
  unfold GExq_FirstCode.code
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (apply lift_bind_count;intro x)
    | (query_count_then_for 115 SdkD_PrepareLower.lower
       <;> first | omega | (solve | exact of_bounded _ _ (GExp_QueryBudget.prepare _ _ _ _ _ _ _ _)) | intro x)
    | (query_count_then_for 900 GExq_BatchSource.current
       <;> first | omega | (solve | exact GExq_BatchBudget.map _ _ _ (GExq_BatchBudget.source _ _ _ _ _ _ _)) | intro x)
    | (query_count_then_for 3 GExp_FirstCode.writerCode
       <;> first | omega | (solve | exact of_bounded _ _ (GExp_CheckpointBudget.writer _ _ _ _)) | intro x)
    | split

#print axioms first
end AspisR1.RawJ_FirstBudget
end
