import RPz8_ARQ_Observer
import RPz7_Tx2N_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_QueryProjection
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution GExq_AccountExperiment

/-- The checkpoint query projection is exact on the existing physical writer
encoding, without computing a concrete large checkpoint. -/
theorem writer_queries (H : Bytes → State) (stored pub : Bytes)
    (p : OraclePortCheckpointAbiC5.Prepared)
    (acc : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E) :
    OraclePortCheckpointPreparedC5.decodeQueries
      (OraclePortCompactDraft.slice (bytesOf (Tx2N_Reader.writer H stored pub p acc).val) 320 88) =
      some p.queries := by
  rw [Tx2N_Reader.writer_bytes,
    (OraclePortCheckpointSlicesC5.prepared_slices H stored pub p acc).2.1,
    OraclePortCheckpointPreparedC5.decodeQueries_encode]

/-- On the original accepted first reply the observer uses that reply's
query vector. The second response and its reads remain unrestricted. -/
theorem on_reply {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      ok (.Ok (saved,post,final)))
    (parser : OraclePortCompactDraft.parse (submitted (eval H a.first).2).stored = some p)
    (decoded : OraclePortCheckpointPreparedC5.decodeQueries
      (OraclePortCompactDraft.slice (bytesOf saved.val) 320 88) = some q) :
    ARQ_Observer.project (eval H (account c hashv copy allocator id a)).2 = (p,q) := by
  rw [accepted_eval c hashv copy allocator id a H saved post final first]
  simp only [ARQ_Observer.project,first,parser,decoded,Option.getD_some]

#print axioms writer_queries
#print axioms on_reply
end AspisR1.ARQ_QueryProjection
end
