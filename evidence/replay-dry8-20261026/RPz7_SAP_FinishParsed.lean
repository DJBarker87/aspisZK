import RPz7_SAP_FinishConsumer
import RPz7_T2R_Finish
import RPz7_AuS1_Finish
import RPz7_Cons_Finish
import RPz7_T2R_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_FinishParsed
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
open AuS1_Finish
theorem consume {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State)) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : Context)
    (old : T2R_Finish.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace)
    (wire : parsed.wire=bytesOf proof.val)
    (hi : input parsed q tr=some i)
    (hq : queries tr=some q)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes=some q)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared tx1p) i.data q (SelectedChallengeMap.rhoOf i.rho)) :
    SAP_FinishConsumer.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace parsed.semantic q tr i c := by
  have same : (⟨bytesOf proof.val,parsed.semantic⟩ : Parsed)=parsed := by
    cases parsed
    simp_all
  apply SAP_FinishConsumer.consume finish v p a proof savedVec H stored publicBytes tx1p parsed trace
    parsed.semantic q tr i c old
  · rw [same]; exact hi
  · exact hq
  · rw [same]; exact read
  · exact decoded
  · exact prepare

#print axioms consume
end AspisR1.SAP_FinishParsed
end
