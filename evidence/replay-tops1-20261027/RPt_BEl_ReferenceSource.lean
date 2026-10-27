import RPt_BEl_Batch
import RPz7_SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_ReferenceSource
open Aeneas Aeneas.Std Result SdkC_Source

/-- Direct reference model on exactly the borrowed source operand arrays.
Only their read fields are projected; no synthetic Prepared is constructed. -/
def code (hashv : Parts → Result Digest) (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array Digest 2#usize) (folded : Digest) (which : Usize) :
    Code (core.result.Result Unit AspisR1Stage2.verifier.Error) := do
  let root0 ← CheckpointBytes5Effect.liftResult (Array.index_usize roots 0#usize)
  let root1 ← CheckpointBytes5Effect.liftResult (Array.index_usize roots 1#usize)
  BEl_Batch.values Port4B_Install.leaves (dictionary hashv) () proof queries
    (Array.make 3#usize [root0,root1,folded]) which

theorem observation {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array Digest 2#usize) (folded : Digest) (which : Usize) :
    BEl_CodeCongr.Equivalent call (code hashv proof queries roots folded which)
      (SdkC_BatchSource.code (dictionary hashv) () proof queries roots folded which) := by
  unfold code SdkC_BatchSource.code
  apply BEl_CodeCongr.bind_tail
  intro root0
  apply BEl_CodeCongr.bind_tail
  intro root1
  exact BEl_Batch.values_observation call Port4B_Install.leaves (dictionary hashv) () proof queries _ which

def currentCode (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) :=
  SdkC_BatchSource.mapCode Op5T_Install.currentError (code hashv proof p.queries p.roots root 0#usize)

def stageCode (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Digest) :=
  SdkC_BatchSource.mapCode Op5T_Install.stageError (code hashv proof p.queries p.roots root 1#usize)

theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) :
    BEl_CodeCongr.Equivalent call (currentCode hashv proof p root)
      (SdkC_BatchSource.currentCode hashv proof p root) := by
  unfold currentCode SdkC_BatchSource.currentCode SdkC_BatchSource.mapCode
  apply BEl_CodeCongr.bind_head
  exact observation call hashv proof p.queries p.roots root _

theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Digest) :
    BEl_CodeCongr.Equivalent call (stageCode hashv proof p root)
      (SdkC_BatchSource.stageCode hashv proof p root) := by
  unfold stageCode SdkC_BatchSource.stageCode SdkC_BatchSource.mapCode
  apply BEl_CodeCongr.bind_head
  exact observation call hashv proof p.queries p.roots root _

#print axioms observation
#print axioms current
#print axioms stage
end AspisR1.BEl_ReferenceSource
end
