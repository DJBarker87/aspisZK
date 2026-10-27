import RPz7_GExq_BatchBudget
import RPz7_GExq_BatchSource
import RPz7_GExq_RetainedReader
import RPz7_GExp_CheckpointBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_GenericBatch
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws

theorem current {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) : count 900 (GExq_BatchSource.current D hash proof p root) :=
  GExq_BatchBudget.map _ _ _ (GExq_BatchBudget.source _ _ _ _ _ _ _)

theorem stage {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (root : Array U8 32#usize) : count 900 (GExq_BatchSource.stage D hash proof p root) :=
  GExq_BatchBudget.map _ _ _ (GExq_BatchBudget.source _ _ _ _ _ _ _)

theorem reader (reserved : Bool) (ck proof pub : Slice U8) (v : VTop_Stages.transport.Variant) :
    GExp_QueryBudget.bounded 3 (GExq_RetainedReader.code reserved ck proof pub v) :=
  GExp_CheckpointBudget.reader reserved ck proof pub v

#print axioms current
#print axioms stage
#print axioms reader
end AspisR1.RPx_GenericBatch
end
