import Port6CK_Saved
import Port5Q1_Complete
import Port6CK_Ten
import OraclePortFrozen2Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Complete
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
open CheckpointBytes3Namespaces
variable {CoreError W : Type}
attribute [local irreducible] OraclePortCheckpointStateC3.advance OraclePortCheckpointStateC3.write
  QueryResidualBridge.values QueryResidualBridge.basis

/-- Saved-to-resumed-to-completed correspondence. The second actual source
block consumes CURRENT op18's returned physical pair. The first block and
saved-ten state come only from ONE actual TX1's writer provenance. -/
theorem accepted (base : Ops) (reserved : Bool) (panic : Port6CK_Checkpoint.Panic)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (ports : Port6CK_Owner.SessionAPrimitives queryOps geometryOps)
    {Hsh : Type} (D : aspis_core.digest.Digest32 Hsh) (hash : Hsh) (H : Bytes → State)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof pub : Slice U8) (stored publicBytes : Bytes) (split : Usize)
    (i : RecordedBinaryExperimentBin.SourceInputs) (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix)
    (prepare : Port6CK_Owner.SessionAPrepare base D hash semantic proof i.data q (SelectedChallengeMap.rhoOf i.rho))
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some i.data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (caller : CheckpointBytes5Join.S2S10CallerBinding (VTop_Checkpoint.digest D) hash H proof pub stored publicBytes)
    (saved : alloc.vec.Vec U8) (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (tx1 : verifier.candidate.tx1
      (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish)
      D semantic pub proof split hash none=ok (.Ok saved))
    (resumed : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish).op18 D
      (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1)))
    (g2 : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry1 : verifier.QueryGeometry) (b1 b12 : verifier.BatchedWeights)
    (out22 : verifier.Accumulator) (flushed22 : Slice aspis_core.field.QM31)
    (geometryCall1 : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish).op11
      p1.queries 10#usize 22#usize=ok (.Ok geometry1))
    (pending1 : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish).op10
      a1.weights.deref=ok (.Ok b1))
    (calls1 : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish).op6
      proof p1 a1 g2 none geometry1 b1 22#usize=ok (.Ok (out22,b12)))
    (flush1 : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish).op9
      b12 out22.weights.deref=ok flushed22) :
    let model := OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q
    CheckpointBytes5Output.accumulator a1=(OraclePortCheckpointStateC3.write model).accumulator ∧
    CheckpointBytes5Output.accumulator (Port5Q1_Endpoint.materialize out22 flushed22)=
      OraclePortCheckpointStateC3.advance model 12 (CheckpointBytes5Output.accumulator a1) ∧
    CheckpointBytes5Output.accumulator (Port5Q1_Endpoint.materialize out22 flushed22)=OraclePortFrozen2.completeState i q ∧
    flushed22.val.length=64 ∧ out22.next.val=22 := by
  have savedTen := Port6CK_Saved.accepted base reserved panic batch geometryOps queryOps finish ports
    D hash H semantic proof pub stored publicBytes split i parsed q tr prepare read wire proofLength
    recovered authenticated caller saved p1 a1 tx1 resumed
  change Port3_GeometryStage.geometry
    (Port4C_GeometryInverse.install (Port4C_CollectStd.install geometryOps)) p1.queries 10#usize 22#usize=ok (.Ok geometry1) at geometryCall1
  rw [Port6CK_Owner.geometry_install] at geometryCall1
  have geo1 := Port5Q1_GeometryReads.accepted geometryOps ports.geometryPrimitives ports.domain
    ports.multiply ports.one ports.inverse p1.queries 10#usize 22#usize geometry1 (by decide) geometryCall1
  change Port3_QueryInstall.result
    (Port3_NativeQueryBody.verifier.candidate.query_loop
      (Port3_QueryStage.release (Port4C_RowStd.install (install queryOps)))
      proof p1 a1 g2 (Port3_QueryInstall.observer none) geometry1 b1 22#usize)=ok (.Ok (out22,b12)) at calls1
  have native := (Port3_QueryInstall.success_iff _ _).mp calls1
  have commute : Port3_QueryStage.release (Port4C_RowStd.install (install queryOps))=
      Port4C_RowStd.install (Port3_QueryStage.release (install queryOps)) := rfl
  rw [commute,Port6CK_Owner.release_install] at native
  have releasePorts := Port6CK_Owner.release_ports queryOps ports.queryPrimitives
  have second := Port5Q1_QueryBlock.materialized (Port3_QueryStage.release queryOps) releasePorts
    proof p1 a1 out22 g2 (Port3_QueryInstall.observer none) geometry1 b1 b12 parsed q tr i.data
    (SelectedChallengeMap.rhoOf i.rho) savedTen.2.2.2.2.2 read wire proofLength recovered authenticated
    10#usize 22#usize geo1 savedTen.2.2.1 savedTen.2.1 savedTen.2.2.2.2.1 savedTen.2.2.2.1
    reserved pending1 native flushed22 flush1
  refine ⟨savedTen.1,second.1,?_,second.2.1,second.2.2.1⟩
  have completed : CheckpointBytes5Output.accumulator (Port5Q1_Endpoint.materialize out22 flushed22)=
      QueryAccumulator.run22
        (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q).iota
        (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q).rho
        (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q).values
        (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q).basis := by
    unfold Port5Q1_Endpoint.materialize
    rw [second.1,savedTen.1]
    exact Port5Q1_Recurrence.twenty_two _
  simpa only [OraclePortFrozen2.completeState,OraclePortCheckpointResumeC5.model,
    OraclePortCheckpointStateC3.fromData] using completed

#print axioms accepted
end AspisR1.Port6CK_Complete
end
