import Cons_Ten
import T2R_Finish
import Cons_Continuation
import Cons_Native
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_Continuation
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
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness) : Prop :=
        ∀ (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
          (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
          (domain : Port5Q1_Domain.SessionADomain geoOps)
          (multiply : geoOps.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
          (one : geoOps.op7 = ok 1#u32) (inverse : geoOps.op11 = Port4C_InverseExecution.inverse_owned),
        ∃ authParsed frame,
          OraclePortCompactDraft.parse (bytesOf f.proof.val) = some authParsed ∧
          FS2.Duplex.Read ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
            (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) frame ∧
          BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot authParsed 2) ∧
          Cons_Ten.Outcome run H ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) authParsed ∧
          T2R_Finish.Outcome finishOps tx2.v2 tx2.p2 {tx2.returned2 with weights := tx2.back2 tx2.flushed2}
            s.proof saved H (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed
            ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero))
theorem strengthen {F C : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prior : Program Bytes State Unit) (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (tx2 : Cons_Native.Witness)
    (calls : Cons_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control
          (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps)
        (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) () s.pub s.proof s.checkpoint tx2)
    (old : Cons_Continuation.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2) :
    Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2 := by
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨parsed,frame,parser,frameRead,target,ten,finish⟩ :=
    old queryLeaves geoLeaves domain multiply one inverse
  refine ⟨parsed,frame,parser,frameRead,target,ten,?_⟩
  exact T2R_Finish.strengthen (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps _ ()
    s.checkpoint s.proof s.pub saved tx2.p2 tx2.saved2 _ tx2.v2 H
    (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed _ calls.1 finish

#print axioms strengthen
end AspisR1.T2R_Continuation
end
