/- New-prefix accepted-only consumer; source of origin: lean/SAP_DirectConsumer.lean. -/
import RPz7_SAF_C_SAP_DirectOutcome
import RPz7_SAF_C_SAP_ClosedOutcome
import RPz7_SAP_NumericTransport
import RPz7_SAF_C_SAP_FinishSaved
import RPz7_SAP_SaveOnRun
import RPz7_SAP_Attach
import RPz7_SAF_C_SAP_FinishParsed
import SAP_InputQuery
import RPz7_T2R_Ten
import RPz7_Cons_Native
import RPz7_SAP_Discovery
import RPz7_F3P_PreparedSource
import RPz7_SAP_Immutable
import RPz7_SAP_SameDigest
import RPz7_SAP_Rebind
import RPz7_PAln_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_C_SAP_DirectConsumer
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem direct {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (authParsed : Parsed)
    (tx2 : Cons_Native.Witness)
    (old : SAF_C_SAP_ClosedOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    SAF_C_SAP_DirectOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  obtain ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,
    out,same,equal,rest⟩ := old
  have current : SAP_CurrentNumeric.numeric run.p=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q := by
    rw [←same,SAP_NumericTransport.numeric]
    exact equal
  exact ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,current,
    prepare,fields,out,same,equal,rest⟩

#print axioms direct
end AspisR1.SAF_C_SAP_DirectConsumer
end
