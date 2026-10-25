import RawJ_FirstBudget
import GExq_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_SecondBudget
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect GExp_CountLaws
local instance : MonadLift Result Code where monadLift := liftResult
theorem reader (reserved : Bool) (ck proof pub : Slice U8) (v : transport.Variant) :
    count 3 (GExq_RetainedReader.code reserved ck proof pub v) := by
  simpa only [GExq_RetainedReader.code,GExp_RetainedReader.code] using
    of_bounded _ _ (GExp_CheckpointBudget.reader reserved ck proof pub v)

#print axioms reader
attribute [local irreducible] GExq_RetainedReader.code GExq_BatchSource.stage

theorem common (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (pub proof ck : Slice U8) :
    count 903 (GExq_SecondCode.common base reserved hashv D pub proof ck hash) := by
  unfold GExq_SecondCode.common
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (apply lift_bind_count;intro x)
    | (query_count_then_for 3 GExq_RetainedReader.code
       <;> first | omega | (solve | apply reader) | intro x)
    | (query_count_then_for 900 GExq_BatchSource.stage
       <;> first | omega | (solve | unfold GExq_BatchSource.stage; apply GExq_BatchBudget.map; apply GExq_BatchBudget.source) | intro x)
    | split

theorem reader (reserved : Bool) (ck proof pub : Slice U8) (v : transport.Variant) :
    count 3 (GExq_RetainedReader.code reserved ck proof pub v) := by
  simpa only [GExq_RetainedReader.code,GExp_RetainedReader.code] using
    of_bounded _ _ (GExp_CheckpointBudget.reader reserved ck proof pub v)

#print axioms reader
attribute [local irreducible] GExq_SecondCode.common

theorem second (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (pub proof ck : Slice U8) :
    count 903 (GExq_SecondCode.code base reserved hashv D pub proof ck hash) := by
  unfold GExq_SecondCode.code
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (solve | apply common)
    | (apply lift_bind_count;intro x)
    | split

#print axioms common
#print axioms second
end AspisR1.RawJ_SecondBudget
end
