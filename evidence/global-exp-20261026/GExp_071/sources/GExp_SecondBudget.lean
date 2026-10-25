import GExp_FirstBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_SecondBudget
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect GExp_CountLaws
local instance : MonadLift Result Code where monadLift := liftResult
attribute [local irreducible] GExp_RetainedReader.code SdkC_BatchSource.stageCode

theorem common (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8) :
    count 11235 (GExp_SecondCode.common base reserved hashv D pub proof ck) := by
  unfold GExp_SecondCode.common
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (apply lift_bind_count;intro x)
    | (query_count_then_for 3 GExp_RetainedReader.code
       <;> first | omega | (solve | exact of_bounded _ _ (GExp_CheckpointBudget.reader _ _ _ _ _)) | intro x)
    | (query_count_then_for 11232 SdkC_BatchSource.stageCode
       <;> first | omega | (solve | apply GExp_BatchBudget.stage) | intro x)
    | split

attribute [local irreducible] GExp_SecondCode.common

theorem second (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8) :
    count 11235 (GExp_SecondCode.code base reserved hashv D pub proof ck) := by
  unfold GExp_SecondCode.code
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (solve | apply common)
    | (apply lift_bind_count;intro x)
    | split

#print axioms common
#print axioms second
end AspisR1.GExp_SecondBudget
end
