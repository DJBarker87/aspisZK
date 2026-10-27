import SdkD_ReplayPair
import AuS1_Recovery
import AuS1_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Pair
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

theorem same_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s)
    (same : bytesOf s.checkpoint.val = bytesOf saved.val)
    (sameProof : bytesOf s.proof.val = bytesOf f.proof.val)
    (parsed : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse (bytesOf f.proof.val) = some parsed) :
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      let trace := AuS1_Recovery.log (Uni_Install.current ops reserved query geo) B std
        (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std)
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
      ∃ frame, FS2.Duplex.Read trace frame ∧
        BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot parsed 2) ∧
      ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
        (q : Fin 22 → Fin 262144),
        Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
        AuS1_Finish.Collision H trace parsed q ∨
        (∀ pos, pos < 22 → OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2
          (OraclePortSelectedDraft.index q 2 pos) = some (OraclePortPackedChoiceC4.payload parsed 2 pos)) := by
  obtain ⟨run,replay⟩ := SdkD_ReplayPair.same_pair adapter ops stage finish reserved query geo B std
    native1 native2 hashv extraction sha256 H p1 syscall accounts1 accounts2 saved f s cuts same sameProof parsed parser
  have binding := S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction
  obtain ⟨frame,read,target,recover⟩ := AuS1_Recovery.authenticated
    (Uni_Install.current ops reserved query geo) B std
    (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std)
    hashv (fun h => by cases h; exact binding ())
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof ()
    (Array.repeat 29#usize run.zero) run.scratch run.p run.prepare_call parsed parser sha256 H p1 syscall
  refine ⟨run,frame,read,target,?_⟩
  intro data rho q prepare
  exact recover q (replay data rho q prepare)

#print axioms same_pair
end AspisR1.AuS1_Pair
end
