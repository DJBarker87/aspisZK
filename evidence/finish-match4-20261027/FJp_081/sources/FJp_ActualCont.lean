import FIs_Cont
import FJp_ActualLiteral
import FJp_RootBinding
import AuS1_OnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_ActualCont
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
          FJp_NativeLiteral.Outcome adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
            saved f s run H
            ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps)
              (F3M_CircleSource.install B) claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps
                (F3M_CircleSource.install B) claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero))
            authParsed tx2
theorem strengthen {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8) (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run
      (Tx1Q_Execution.actual (Op5T_Concrete.current (FIp_Install.configuration err seed r).currentBase)
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std)
      (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
      (FIp_Install.configuration err seed r).geometry
      (SdkD_PairBatches.current (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase
        (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (prior : Program Bytes State Unit) (H : Bytes → State) (t : Cons_Native.Witness)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install (FIp_Install.configuration err seed r).adapter
          (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (FIp_Install.configuration err seed r).stageBase)
            (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
            (FIp_Install.configuration err seed r).geometry)) (FIp_Install.configuration err seed r).finish)
        (Uni_Install.current (FIp_Install.configuration err seed r).currentBase
          (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
          (FIp_Install.configuration err seed r).geometry) (F3M_CircleSource.install B) std)
      accounts1 accounts2 saved f s)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (⟨(FIp_Install.configuration err seed r).adapter,(FIp_Install.configuration err seed r).currentBase,
        (FIp_Install.configuration err seed r).stageBase,(FIp_Install.configuration err seed r).finish,
        (FIp_Install.configuration err seed r).reserved,(FIp_Install.configuration err seed r).query,
        (FIp_Install.configuration err seed r).geometry,F3M_CircleSource.install B,std⟩ : DrvC_Installation.Configuration FIo_Install.W C))
      native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val)
    (size : f.proof.val.length=57607) (rootBinding : FJp_RootBinding.Holds f.proof run.root)
    (old : FIs_Cont.Outcome (FIp_Install.configuration err seed r).adapter
      (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).stageBase
      (FIp_Install.configuration err seed r).finish (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      B std prior H f s saved run t) :
    Outcome (FIp_Install.configuration err seed r).adapter
      (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).stageBase
      (FIp_Install.configuration err seed r).finish (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      B std prior H f s saved run t := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨parsed,frame,parser,read,target,literal⟩ := old
  obtain ⟨rootView,rootRange,rootCopy⟩ := rootBinding
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry (F3M_CircleSource.install B) std) accounts1 accounts2 saved f s := by
    rw [AuS1_Install.dictionary]
    exact cuts
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary c.adapter c.currentBase c.stageBase c.finish
        c.reserved c.query c.geometry (F3M_CircleSource.install B) std) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]
    exact extraction
  obtain ⟨newFrame,newRead,newTarget,auth⟩ := AuS1_OnRun.same_pair prior c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry (F3M_CircleSource.install B) std native1 native2 hashv pairExtraction
    sha256 H p1 syscall accounts1 accounts2 saved f s pairCuts sameSaved sameProof parsed parser run rootView rootRange rootCopy
  refine ⟨parsed,frame,parser,read,target,?_⟩
  refine FJp_ActualLiteral.strengthen err seed r B std saved f s run H _ parsed t accounts1 accounts2 cuts
    parser sameProof sameSaved size ?_ literal
  intro data rho q prepared
  rcases auth data rho q prepared with hit | indexed
  · exact Or.inl hit
  · right
    exact ⟨OraclePortAllSelectedRecoveryC6.recovered _ newFrame parsed 2,indexed⟩
#print axioms strengthen
end AspisR1.FJp_ActualCont
end
