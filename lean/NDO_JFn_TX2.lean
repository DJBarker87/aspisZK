import NDO_JFn_Lines
import NDO_JFn_Resume
import NDO_JFo_ReaderFixture
import RPt_JFo_Powers
import NDO_JFo_Pending
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_TX2
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Partial TX2 source-call fixture on ONE retained byte triple. The actual
reader remains conditional on oracle realization; query gate/geometry,
batch1, finish and accepted2 are not asserted or hidden as hypotheses. -/
theorem partial_on_saved (saved : alloc.vec.Vec U8)
    (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (seed : Port3_NativeQueryBody.Ops) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    OraclePortCheckpointResumeC5.decodeAccumulator (MultiproofConeCanonical.bytesOf JFx_NativeBytes.checkpoint.val)=
      some (CheckpointBytes5Output.accumulator JFo_Prepared.accumulator) ∧
    (∃ g : Array Tx2N_Powers.E 29#usize,
      Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok g) ∧
    Port3_NativePendingInstall.source true JFo_Prepared.accumulator.weights.deref=ok (.Ok JFo_Pending.value) ∧
    ∀ i : Fin 12,
      (JFn_ArrayBuilder.ops seed).op0 4#usize
        (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (JFn_ArrayBuilder.ops seed)) (JFo_Opening.value (JFn_Values.position i))=ok (JFn_Values.value i) ∧
      ∀ inverse : Array U32 5#usize, ∃ out,
        SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value i) inverse=ok out ∧
        Port4C_QueryArithmetic.CanonE out := by
  obtain ⟨g,run,_⟩:=JFo_Powers.source
  exact ⟨JFn_Resume.on_saved saved same H D hash realizes,JFo_DecodedAccumulator.source,
    ⟨g,run⟩,JFo_Pending.source,fun i => ⟨JFn_Values.source seed i,JFn_Lines.source i⟩⟩

#print axioms partial_on_saved
#print partial_on_saved
end AspisR1.JFn_TX2
end
