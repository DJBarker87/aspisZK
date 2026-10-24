import Port5Q1_Ten
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Endpoint
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryAccumulator.run22
  OraclePortCheckpointStateC3.write QueryResidualBridge.values QueryResidualBridge.basis

def materialize (a : verifier.Accumulator) (weights : Slice aspis_core.field.QM31) : verifier.Accumulator :=
  {a with weights:=⟨weights.val,weights.property⟩}

/-- Both source blocks, with a fresh pending constructor in the resumed block.
The second call consumes exactly the first physical materialized state, on the
SAME Prepared/data/query model. Both weight identities come from actual flushes.
Checkpoint reader transport to this saved state is a separate caller row. -/
theorem ten_twelve (base : VTop_Stages.Ops) (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a0 out10 out22 : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry0 geometry1 : verifier.QueryGeometry) (b0 b10 b1 b12 : verifier.BatchedWeights)
    (flushed10 flushed22 : Slice aspis_core.field.QM31)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data FE) (rho : FK)
    (prepare : SessionAPrepare p data q rho)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (geo0 : Port5Q1_GeometryBinding.Binding p.queries 0#usize 10#usize geometry0)
    (geo1 : Port5Q1_GeometryBinding.Binding p.queries 10#usize 22#usize geometry1)
    (reserved : Bool)
    (initial : Port3_Initial.constructor reserved .S2=ok (.Ok a0))
    (pending0 : Port3_NativePendingInstall.source reserved a0.weights.deref=ok (.Ok b0))
    (calls0 : verifier.candidate.query_loop (Port4C_RowStd.install (install ops))
      proof p a0 g obs geometry0 b0 10#usize=ok (.Ok (out10,b10)))
    (flush0 : Port3_FlushInstall.flush b10 out10.weights.deref=ok flushed10)
    (pending1 : Port3_NativePendingInstall.source reserved (materialize out10 flushed10).weights.deref=ok (.Ok b1))
    (calls1 : verifier.candidate.query_loop (Port4C_RowStd.install (install ops))
      proof p (materialize out10 flushed10) g obs geometry1 b1 22#usize=ok (.Ok (out22,b12)))
    (flush1 : Port3_FlushInstall.flush b12 out22.weights.deref=ok flushed22) :
    let model := OraclePortCheckpointResumeC5.model data rho q
    CheckpointBytes5Output.accumulator (materialize out10 flushed10)=(OraclePortCheckpointStateC3.write model).accumulator ∧
    CheckpointBytes5Output.accumulator (materialize out22 flushed22)=
      OraclePortCheckpointStateC3.advance model 12 (CheckpointBytes5Output.accumulator (materialize out10 flushed10)) ∧
    CheckpointBytes5Output.accumulator (materialize out22 flushed22)=
      QueryAccumulator.run22 model.iota model.rho model.values model.basis ∧
    flushed10.val.length=64 ∧ flushed22.val.length=64 ∧ out10.next.val=10 ∧ out22.next.val=22 := by
  have first := Port5Q1_Ten.accepted base ops ports proof p a0 out10 g obs geometry0 b0 b10
    parsed q tr data rho prepare read wire proofLength recovered authenticated geo0 reserved initial
    pending0 calls0 flushed10 flush0
  have second := Port5Q1_QueryBlock.materialized ops ports proof p (materialize out10 flushed10) out22
    g obs geometry1 b1 b12 parsed q tr data rho prepare read wire proofLength recovered authenticated
    10#usize 22#usize geo1 first.2.2.1 first.2.1 first.2.2.2.2 first.2.2.2.1 reserved pending1 calls1 flushed22 flush1
  have saved : CheckpointBytes5Output.accumulator (materialize out10 flushed10)=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data rho q)).accumulator := first.1
  have resumed : CheckpointBytes5Output.accumulator (materialize out22 flushed22)=
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model data rho q) 12
        (CheckpointBytes5Output.accumulator (materialize out10 flushed10)) := second.1
  refine ⟨saved,resumed,?_,first.2.1,second.2.1,first.2.2.1,second.2.2.1⟩
  rw [resumed,saved]
  exact Port5Q1_Recurrence.twenty_two _

#print axioms ten_twelve
end AspisR1.Port5Q1_Endpoint
end
