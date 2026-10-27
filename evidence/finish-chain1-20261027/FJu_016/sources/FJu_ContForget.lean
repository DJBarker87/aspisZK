import FJp_ActualCont
import FJu_Cont
import FJu_LiteralForget
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_ContForget
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

theorem value {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness)
    (new : FJu_Cont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    FJp_ActualCont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  obtain ⟨parsed,frame,parser,read,target,literal⟩ := new
  exact ⟨parsed,frame,parser,read,target,FJu_LiteralForget.value (new := literal)⟩
#print axioms value
end AspisR1.FJu_ContForget
end
