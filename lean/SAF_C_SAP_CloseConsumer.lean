/- New-prefix accepted-only consumer; source of origin: lean/SAP_CloseConsumer.lean. -/
import SAF_C_SAP_ClosedOutcome
import SAF_C_SAP_SourceOutcome
import SAF_C_SAP_FinishSaved
import SAP_SaveOnRun
import SAP_Attach
import SAF_C_SAP_FinishParsed
import SAP_InputQuery
import T2R_Ten
import Cons_Native
import SAP_Discovery
import F3P_PreparedSource
import SAP_Immutable
import SAP_SameDigest
import SAP_Rebind
import PAln_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_C_SAP_CloseConsumer
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem close {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
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
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std)
      native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (old : SAF_C_SAP_SourceOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    SAF_C_SAP_ClosedOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  obtain ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,
    out,same,equal,ten,finishOld⟩ := old
  refine ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,
    out,same,equal,?_⟩
  intro ports geometry domain multiply one inverse
  rcases ten ports geometry domain multiply one inverse with collision | indexed
  · exact Or.inl collision
  · have oracle := F3N_SameOracle.current adapter ops stage finish reserved query geo
      (F3M_CircleSource.install B) std native1 native2 hashv extraction sha256 H p1 syscall
    have sourceSaved := SAP_SaveOnRun.saved (Op5T_Concrete.current ops) reserved query geo B std
      _ () _ f.pub f.proof f.split saved run ports H oracle out same
    rw [equal,indexed.1] at sourceSaved
    refine Or.inr ⟨indexed.1,indexed.2.1,indexed.2.2.1,indexed.2.2.2,sourceSaved,?_⟩
    exact SAF_C_SAP_FinishSaved.consume finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace parsed.semantic q _ i
      (OraclePortAcceptedContextC6.context parsed i view) (finishOld _) sourceSaved

#print axioms close
end AspisR1.SAF_C_SAP_CloseConsumer
end
