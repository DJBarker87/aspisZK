import RPz7_Rc5_Cont
import RPz7_FIs_Literal
import RPz7_SAF_C_SAF_PreparedCont
import RPz7_Rc5_Literal
import RPz7_T2R_Ten
import RPz7_T2R_Finish
import RPz7_Cons_Native
import RPz7_AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIs_Cont
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
          FIs_Literal.Outcome adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
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
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (enriched : FIs_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps D hash s.pub s.proof s.checkpoint tx2)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F) (installed : finishOps=FIn_Install.finishOps seed)
    (positions : stageBase.op22=ok 7527#usize ∧ stageBase.op21=ok 8007#usize ∧ stageBase.op20=ok 10055#usize)
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val)
    (old : Rc5_Cont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  obtain ⟨parsed,frame,parser,read,target,literal⟩ := old
  exact ⟨parsed,frame,parser,read,target,FIs_Literal.strengthen adapterOps ops reserved queryOps geoOps
    stageBase finishOps B claimsStd saved f s run H _ parsed tx2 D hash enriched seed installed positions sameProof sameSaved literal⟩

#print axioms strengthen
end AspisR1.FIs_Cont
end
