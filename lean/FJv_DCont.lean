import FJv_DDefinitions
import SAF_C_SAF_PreparedCont
import Rc5_Literal
import T2R_Ten
import T2R_Finish
import Cons_Native
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJv_DCont
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

def Outcome {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness) : Prop :=
        ∃ authParsed frame,
          OraclePortCompactDraft.parse (bytesOf f.proof.val) = some authParsed ∧
          FS2.Duplex.Read ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd
            (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) frame ∧
          BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot authParsed 2) ∧
          FJv_DLiteral.Outcome adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
            saved f s run H
            ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps)
              (F3M_CircleSource.install B) claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps
                (F3M_CircleSource.install B) claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero))
            authParsed tx2
theorem strengthen {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness)
    (indexError : C) (queryBase : Port3_NativeQueryBody.Ops)
    (geoBase : Port3_NativeGeometryBody.Ops C)
    (querySource : queryOps=SAQ_Decoder.install queryBase)
    (geoSource : geoOps=SAQ_Constructor.install indexError geoBase)
    (old : FJv_DPairCont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  have ports : Port5Q1_QueryPorts.SessionAPrimitives queryOps := by
    rw [querySource]; exact SAQ_Decoder.primitives queryBase
  have geometry : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps := by
    rw [geoSource]; exact SAQ_Constructor.canonical indexError geoBase
  have domain : Port5Q1_Domain.SessionADomain geoOps := by
    rw [geoSource]; exact SAQ_Constructor.domain indexError geoBase
  have multiply : geoOps.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := by
    rw [geoSource]; exact SAQ_Constructor.multiply indexError geoBase
  have one : geoOps.op7=ok (1#u32) := by
    rw [geoSource]; exact SAQ_Constructor.one indexError geoBase
  have inverse : geoOps.op11=Port4C_InverseExecution.inverse_owned := by
    rw [geoSource]; exact SAQ_Constructor.inverse indexError geoBase
  obtain ⟨parsed,frame,parser,read,target,literal⟩ := old ports geometry domain multiply one inverse
  exact ⟨parsed,frame,parser,read,target,literal⟩

#print axioms strengthen
end AspisR1.FJv_DCont
end
