import T2R_LegacyTen
import T2R_Legacy
import T2R_ContSource
import Cons_Continuation
import T2R_Ten
import T2R_Finish
import Cons_Native
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_LegacyCont
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

theorem forget {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness)
    (new : T2R_ContSource.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) : Cons_Continuation.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨parsed,frame,parser,read,target,ten,finish⟩ := new queryLeaves geoLeaves domain multiply one inverse
  exact ⟨parsed,frame,parser,read,target,T2R_LegacyTen.forget run H _ parsed ten,
    T2R_Legacy.finish finishOps tx2.v2 tx2.p2 _ s.proof saved H (bytesOf f.proof.val)
      (bytesOf f.pub.val) run.p parsed _ finish⟩

#print axioms forget
end AspisR1.T2R_LegacyCont
end
