import BEn_ExtractedTrace
import BEl_NativeBatchCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_ExtractedSlots
open Aeneas Aeneas.Std Result SdkC_Source
abbrev Input := BEl_NativeBatchCut.Input
abbrev ordinal := BEl_NativeBatchCut.ordinal

/-- Extracted batch parent with its actual Prepared read fields projected.
This is the Port3 parent monadic syntax, with its digest-bearing children
reified by Port9OR. It constructs no replacement Prepared witness. -/
def body (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2) :
    Code (core.result.Result Unit AspisR1Stage2.verifier.Error) := do
  let root0 ← CheckpointBytes5Effect.liftResult (Array.index_usize input.roots 0#usize)
  let root1 ← CheckpointBytes5Effect.liftResult (Array.index_usize input.roots 1#usize)
  Port9OR_Batch.values Port4B_Install.leaves (dictionary hashv) () input.proof input.queries
    (Array.make 3#usize [root0,root1,input.folded]) (ordinal slot)

/-- Use the sole D188_TRACE_BOUNDARY attribution in BEn_ExtractedTrace:
this is the same recorder, now at the projected parent operands. -/
def observe {S E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result Unit E)) (state : S) (before : Log) :=
  BEl_PartialRecorder.observation (BEl_PartialRecorder.run call code state (BEl_Recorder.completed before))

def native {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest)
    (input : Input) (slot : Fin 2) (state : S) (before : Log) :=
  observe call (body hashv input slot) state before

def currentBody (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) :=
  SdkC_BatchSource.mapCode Op5T_Install.currentError
    (body hashv ⟨proof,p.queries,p.roots,root⟩ ⟨0,by decide⟩)

def stageBody (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Digest) :=
  SdkC_BatchSource.mapCode Op5T_Install.stageError
    (body hashv ⟨proof,p.queries,p.roots,root⟩ ⟨1,by decide⟩)

theorem source (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2) :
    body hashv input slot = SdkC_BatchSource.code (dictionary hashv) ()
      input.proof input.queries input.roots input.folded (ordinal slot) := rfl

theorem parent (hashv : Parts → Result Digest) (input : BEn_ExtractedTrace.Input) (slot : Fin 2) :
    body hashv ⟨input.proof,input.prepared.queries,input.prepared.roots,input.folded⟩ slot =
      BEn_ExtractedTrace.body hashv input slot := rfl

theorem current (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) :
    currentBody hashv proof p root = SdkC_BatchSource.currentCode hashv proof p root := rfl

theorem stage (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Digest) :
    stageBody hashv proof p root = SdkC_BatchSource.stageCode hashv proof p root := rfl

#print axioms source
#print axioms parent
#print axioms current
#print axioms stage
end AspisR1.BEn_ExtractedSlots
end
