import F3N_TenDiscovered
import F3N_SourceInput
import F3N_TenInput
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ReaderDiscovered
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical OraclePortCompactDraft

theorem same_input {C Hash : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (f : S2W_NativeConsolidation.FirstCut) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (resumed : AspisR1Stage2.verifier.Accumulator)
    (readback : CheckpointBytes5Output.accumulator resumed=CheckpointBytes5Output.accumulator
      (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}))
    (H : Bytes → State) (trace : List (Bytes × State)) (modelInput : F3_Model.Input)
    (facts : F3N_SourceInput.Facts f run.p H modelInput)
    (ten : ∀ p,parse (bytesOf f.proof.val)=some p → Cons_Ten.Outcome run H trace p)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo) (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned) :
    let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program modelInput.proof 0 33
      (FS.emptyPrefix modelInput.semantic.value))).2
    (∃ p q i,OraclePortStoredParserC4.parseReached modelInput.stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some i ∧
      AuS1_Finish.Collision H trace p q) ∨
    (∃ p q i,OraclePortStoredParserC4.parseReached modelInput.stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some i ∧
      CheckpointBytes5Output.accumulator resumed=
        (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
          (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) := by
  have source := F3N_TenDiscovered.same_input installed reserved query geo D hash f saved run H trace
    modelInput facts ten ports canonical domain multiply one inverse
  simpa only [readback] using source

#print axioms same_input
end AspisR1.F3N_ReaderDiscovered
end
