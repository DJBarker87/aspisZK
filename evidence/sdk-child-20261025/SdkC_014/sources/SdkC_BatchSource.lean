import SdkC_Oracle
import Port9OR_Batch
import Op5T_Concrete
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_BatchSource
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Complete fixed physical batch source: exact input arrays, source order,
duplicate hash-before-compare, native P6 calls and every rejection prefix. -/
def code {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 2#usize) (folded : Array U8 32#usize) (which : Usize) :
    SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error) := do
  let root0 ← CheckpointBytes5Effect.liftResult (Array.index_usize roots 0#usize)
  let root1 ← CheckpointBytes5Effect.liftResult (Array.index_usize roots 1#usize)
  Port9OR_Batch.values Port4B_Install.leaves D hash proof queries
    (Array.make 3#usize [root0,root1,folded]) which

/-- Erasure to the ACTUAL installed source body for arbitrary inputs/results.
No parse/queries/roots/acceptance/model equivalence premise. -/
theorem erasure {Hash : Type} (D E : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 2#usize) (folded : Array U8 32#usize) (which : Usize) :
    CheckpointBytes5Effect.erase E hash (code D hash proof queries roots folded which) =
      Op5T_Install.body Port4B_Install.leaves E proof queries roots folded which hash := by
  simp only [code,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_lift,
    Port9OR_Batch.values_source]
  rfl

def mapCode {Err : Type} (map : AspisR1Stage2.verifier.Error → Err)
    (body : SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    SdkC_Source.Code (core.result.Result Unit Err) := do
  let value ← body
  pure (match value with | .Ok x => .Ok x | .Err e => .Err (map e))

theorem map_erasure {Hash Err : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (map : AspisR1Stage2.verifier.Error → Err)
    (body : SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    CheckpointBytes5Effect.erase D hash (mapCode map body) =
      Op5T_Install.mapResult map (CheckpointBytes5Effect.erase D hash body) := by
  simp only [mapCode,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_pure]
  cases CheckpointBytes5Effect.erase D hash body with
  | fail e => rfl
  | div => rfl
  | ok value => cases value <;> rfl

def currentCode (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) :
    SdkC_Source.Code (core.result.Result Unit AspisR1CurrentCaller.verifier.Error) :=
  mapCode Op5T_Install.currentError
    (code (SdkC_Source.dictionary hashv) () proof p.queries p.roots root 0#usize)

def stageCode (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_Source.Code (core.result.Result Unit VTop_Stages.verifier.Error) :=
  mapCode Op5T_Install.stageError
    (code (SdkC_Source.dictionary hashv) () proof p.queries p.roots root 1#usize)

theorem current_source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize)
    (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (currentCode hashv proof p root) before).1 =
      Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize () := by
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Unit :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  rw [SdkC_Source.erasure_to E () hashv source]
  simp only [currentCode,map_erasure,erasure]
  rfl

theorem stage_source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (stageCode hashv proof p root) before).1 =
      Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize () := by
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Unit :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  rw [SdkC_Source.erasure_to E () hashv source]
  simp only [stageCode,map_erasure,erasure]
  rfl

#print axioms erasure
#print axioms map_erasure
#print axioms current_source
#print axioms stage_source
end AspisR1.SdkC_BatchSource
end
