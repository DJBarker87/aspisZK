import T2R_ContSource
import TxS_ContSource
import TxS_LegacyFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_LegacyCont
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
    (new : TxS_ContSource.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    T2R_ContSource.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨parsed,frame,parser,frameRead,target,ten,finish⟩ := new queryLeaves geoLeaves domain multiply one inverse
  exact ⟨parsed,frame,parser,frameRead,target,
    TxS_RawTen.to_typed run H _ parsed ten,
    TxS_LegacyFinish.forget finishOps _ _ _ s.proof saved H _ _ run.p parsed _ finish⟩

#print axioms forget
end AspisR1.TxS_LegacyCont
end
