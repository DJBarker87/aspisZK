import FJp_ActualCont
import FJu_NativeLiteral
import FIs_Cont
import FJp_ActualLiteral
import FJp_RootBinding
import AuS1_OnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_Cont
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
          FJu_NativeLiteral.Outcome adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
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
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (old : FJp_ActualCont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  obtain ⟨parsed,frame,parser,read,target,literal⟩ := old
  exact ⟨parsed,frame,parser,read,target,FJu_NativeLiteral.strengthen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sameProof literal⟩

#print axioms strengthen
end AspisR1.FJu_Cont
end
