import SAF_ForgetFinish
import SAF_C_SAF_PreparedOutcome
import SAP_LiteralOutcome
import SAP_LiteralFields
import SAP_NumericTransport
import SAP_FinishSaved
import SAP_SaveOnRun
import SAP_Attach
import SAP_FinishParsed
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
namespace AspisR1.SAF_ForgetOutcome
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem forget {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
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
    (after : SAF_C_SAF_PreparedOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    SAP_LiteralOutcome.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  rcases after with ⟨model,parsed,q,i,view,physical,stored,parse,hq,hi,read,opening,fields,numeric,
    prepare,prep,sourcePrepared,current,numerics,rest⟩
  refine ⟨model,parsed,q,i,view,physical,stored,parse,hq,hi,read,opening,fields,numeric,
    prepare,prep,sourcePrepared,current,numerics,?_⟩
  intro ports geometry domain multiply one inverse
  rcases rest ports geometry domain multiply one inverse with collision | good
  · exact Or.inl collision
  · right
    rcases good with ⟨acc,writer,len,next,savedEq,finishing⟩
    refine ⟨acc,writer,len,next,savedEq,?_⟩
    apply SAF_ForgetFinish.forget (after := finishing)

#print axioms forget
end AspisR1.SAF_ForgetOutcome
end
