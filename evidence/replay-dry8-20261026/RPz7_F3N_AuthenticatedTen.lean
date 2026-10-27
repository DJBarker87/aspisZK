import RPz7_F3N_Ten
import RPz7_AuS1_OnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_AuthenticatedTen
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical
theorem same_run {F C : Type} (prior : Program Bytes State Unit) (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
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
    (parser : OraclePortCompactDraft.parse (bytesOf f.proof.val) = some parsed)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (view : Slice U8)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      f.proof {start:=7751#usize,«end»:=7783#usize} = ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok run.root)) :
    let trace := (eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved query geo) B std
      (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std)
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
    ∃ frame, FS2.Duplex.Read trace frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot parsed 2) ∧
      Cons_Ten.Outcome run H trace parsed := by
  obtain ⟨frame,frameRead,target,auth⟩ := AuS1_OnRun.same_pair prior adapter ops stage finish reserved query geo
    B std native1 native2 hashv extraction sha256 H p1 syscall accounts1 accounts2 saved f s cuts
    same sameProof parsed parser run view range copy
  have length : f.proof.val.length=57607 := by
    simpa only [bytesOf,List.length_map] using cuts.proofLength
  refine ⟨frame,frameRead,target,F3N_Ten.transport run length H _ parsed ?_⟩
  intro data rho q prepare
  rcases auth data rho q prepare with collision | indexed
  · exact Or.inl collision
  · exact Or.inr ⟨OraclePortAllSelectedRecoveryC6.recovered _ frame parsed 2,indexed⟩

#print axioms same_run
end AspisR1.F3N_AuthenticatedTen
end
