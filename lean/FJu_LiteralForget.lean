import FJp_NativeLiteral
import FJu_NativeLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_LiteralForget
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem value {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
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
    (new : FJu_NativeLiteral.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2) :
    FJp_NativeLiteral.Outcome adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2 := by
  obtain ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,remaining⟩ := new
  refine ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,?_⟩
  rcases remaining with hit | good
  · exact Or.inl hit
  · right
    obtain ⟨acc,writer,len,next,savedEq,finishing⟩ := good
    exact ⟨acc,writer,len,next,savedEq,FJu_Finish.forget (new := finishing)⟩
#print axioms value
end AspisR1.FJu_LiteralForget
end
