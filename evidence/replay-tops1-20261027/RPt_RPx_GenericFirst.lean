import RPz7_GExp_CheckpointBudget
import RPt_RPx_GenericBatch
import RPz7_GExq_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_GenericFirst
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect GExp_CountLaws
local instance : MonadLift Result Code where monadLift := liftResult
attribute [local irreducible] SdkD_PrepareLower.lower GExq_BatchSource.current GExp_FirstCode.writerCode

theorem first {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash) :
    count 1018 (GExq_FirstCode.code base B std hashv D semantic pub proof split hash) := by
  unfold GExq_FirstCode.code
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (apply lift_bind_count;intro x)
    | (query_count_then_for 115 SdkD_PrepareLower.lower
       <;> first | omega | (solve | exact of_bounded _ _ (GExp_QueryBudget.prepare _ _ _ _ _ _ _ _)) | intro x)
    | (query_count_then_for 900 GExq_BatchSource.current
       <;> first | omega | (solve | apply RPx_GenericBatch.current) | intro x)
    | (query_count_then_for 3 GExp_FirstCode.writerCode
       <;> first | omega | (solve | exact of_bounded _ _ (GExp_CheckpointBudget.writer _ _ _ _)) | intro x)
    | split

#print axioms first
end AspisR1.RPx_GenericFirst
end
