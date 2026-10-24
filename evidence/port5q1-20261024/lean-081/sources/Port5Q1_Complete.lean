import Port5Q1_Frozen2
import Port5Q1_GeometryReads
import OraclePortFrozen2Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Complete
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts Port5Q1_Endpoint
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryAccumulator.run22
  OraclePortCheckpointStateC3.write QueryResidualBridge.values QueryResidualBridge.basis

theorem accepted {CoreError : Type} (base : VTop_Stages.Ops) (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a0 out10 out22 : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry0 geometry1 : verifier.QueryGeometry) (b0 b10 b1 b12 : verifier.BatchedWeights)
    (flushed10 flushed22 : Slice aspis_core.field.QM31)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (prepare : SessionAPrepare p i.data q (SelectedChallengeMap.rhoOf i.rho))
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some i.data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError)
    (geometryCanonical : Port5Q1_GeometryCanonical.SessionAPrimitives geometryOps)
    (domain : Port5Q1_Domain.SessionADomain geometryOps)
    (multiply : geometryOps.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geometryOps.op7=ok (1#u32))
    (inverse : geometryOps.op11=Port4C_InverseExecution.inverse_owned)
    (geometryCall0 : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometryOps)
      p.queries 0#usize 10#usize=ok (.Ok geometry0))
    (geometryCall1 : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometryOps)
      p.queries 10#usize 22#usize=ok (.Ok geometry1))
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
    let model := OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q
    CheckpointBytes5Output.accumulator (materialize out10 flushed10)=(OraclePortCheckpointStateC3.write model).accumulator ∧
    CheckpointBytes5Output.accumulator (materialize out22 flushed22)=
      OraclePortCheckpointStateC3.advance model 12 (CheckpointBytes5Output.accumulator (materialize out10 flushed10)) ∧
    CheckpointBytes5Output.accumulator (materialize out22 flushed22)=OraclePortFrozen2.completeState i q ∧
    flushed10.val.length=64 ∧ flushed22.val.length=64 ∧ out10.next.val=10 ∧ out22.next.val=22 := by
  have geo0 := Port5Q1_GeometryReads.accepted geometryOps geometryCanonical domain multiply one inverse
    p.queries 0#usize 10#usize geometry0 (by decide) geometryCall0
  have geo1 := Port5Q1_GeometryReads.accepted geometryOps geometryCanonical domain multiply one inverse
    p.queries 10#usize 22#usize geometry1 (by decide) geometryCall1
  exact Port5Q1_Frozen2.accepted base ops ports proof p a0 out10 out22 g obs geometry0 geometry1 b0 b10 b1 b12
    flushed10 flushed22 parsed q tr i prepare read wire proofLength recovered authenticated geo0 geo1 reserved initial
    pending0 calls0 flush0 pending1 calls1 flush1

#print axioms accepted
end AspisR1.Port5Q1_Complete
end
