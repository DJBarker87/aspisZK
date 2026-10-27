import RPt_BEj_BatchValue
import RPt_BEl_PartialRecorder
import RPt_BEm_Final
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_ExtractedTrace
open Aeneas Aeneas.Std Result SdkC_Source

abbrev Input := BEj_ReifiedBatch.Input
abbrev ordinal := BEj_ReifiedBatch.ordinal

/-- Existing effect reification of the extracted batch parent. Its leaves are
Port4B_LeafCode and Port9OR_P6Verify, not the BEl reference implementation.
Port9OR_Batch.source is the checked erasure to Port3_NativeBatchBody. -/
def body (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2) :=
  Port9OR_Batch.code Port4B_Install.leaves (dictionary hashv) ()
    input.proof input.prepared input.folded (ordinal slot)

/-- D188_TRACE_BOUNDARY: sole attribution point for the owner-approved
2026-10-27 trace-fidelity trust item. For the same extracted body, operands,
replies and pins, native observation is DEFINED by instrumenting that term.
This definition does not assert semantics for an arbitrary opaque function.
Pending attempts precede backend return, including failure and divergence. -/
def native {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2)
    (state : S) (before : Log) :=
  BEl_PartialRecorder.observation (BEl_PartialRecorder.run call
    (body hashv input slot) state (BEl_Recorder.completed before))

theorem recorder {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (input : Input) (slot : Fin 2)
    (state : S) (before : Log) :
    native call hashv input slot state before =
      BEf_Carrier.run call (body hashv input slot) state before :=
  BEl_PartialRecorder.correspondence call _ state before

/-- Result audit of precisely the body instrumented above; not an inference
of trace equality from Result equality. -/
theorem emitted (hashv : Parts → Result Digest) (input : Input)
    (slot : Fin 2) (before : Log) :
    (SdkC_Source.run hashv (body hashv input slot) before).1 =
      Port3_NativeBatchBody.verifier.candidate.batch_merkle
        (Port9OR_BatchStep.ops Port4B_Install.leaves) (dictionary hashv)
        input.proof input.prepared input.folded (ordinal slot) () :=
  BEj_BatchValue.emitted hashv input slot before

#print axioms recorder
#print axioms emitted
end AspisR1.BEn_ExtractedTrace
end
