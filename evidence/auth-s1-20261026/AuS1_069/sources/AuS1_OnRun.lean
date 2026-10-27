import AuS1_Pair
import AuS1_Context
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_OnRun
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

theorem same_pair {F C : Type} (prior : AspisV8R19.Program Bytes State Unit) (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
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
      ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
        (q : Fin 22 → Fin 262144),
        Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
        AuS1_Finish.Collision H trace parsed q ∨
        (∀ pos, pos < 22 → OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2
          (OraclePortSelectedDraft.index q 2 pos) = some (OraclePortPackedChoiceC4.payload parsed 2 pos)) := by
  obtain ⟨p2,a2,root2,view2,read,range2,copy2,batch2⟩ :=
    SdkD_SecondRun.same_cut adapter ops stage finish reserved query geo B std accounts1 accounts2 saved f s cuts
  have binding := S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction
  have wire := (OraclePortCompactDraft.parse_header _ _ parser).2
  have length : f.proof.val.length = 57607 := by
    simpa only [wire,bytesOf,List.length_map] using OraclePortStoredWidthsC4.parsed_length _ parsed parser
  have length1 : s.proof.val.length = 57607 := by
    have lengths := congrArg List.length sameProof
    simp only [bytesOf,List.length_map] at lengths
    omega
  obtain ⟨frame,frameRead,target,recover⟩ := AuS1_Context.authenticated prior
    (Uni_Install.current ops reserved query geo) B std
    (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std)
    hashv (fun h => by cases h; exact binding ())
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof ()
    (Array.repeat 29#usize run.zero) run.scratch run.p run.prepare_call parsed parser sha256 H p1 syscall
  refine ⟨frame,frameRead,target,?_⟩
  intro data rho q prepare
  have first := SdkD_FirstModel.indexed (Uni_Install.current ops reserved query geo) B std hashv _
    (binding ()) sha256 H p1 syscall f.proof length (AspisS6CurrentVerifierCarrier.toPublic f.semantic)
    run.p (Array.repeat 29#usize run.zero) run.scratch run.prepare_call run.root view range copy
    (bytesOf f.proof.val) parsed parser wire data rho q prepare run.batch_call
  have second := SdkD_SecondModel.indexed (Uni_Install.current ops reserved query geo) B std hashv _
    (binding ()) sha256 H p1 syscall f.proof s.proof f.pub s.pub s.checkpoint length length1 saved reserved
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) run.p p2
    (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) a2
    (Array.repeat 29#usize run.zero) run.scratch run.prepare_call root2 view2 range2 copy2
    (bytesOf f.proof.val) parsed parser wire (wire.trans sameProof.symm) data rho q prepare
    run.writer_call same read batch2
  exact recover q (SdkD_BatchUnion.accepted H parsed q first second)

#print axioms same_pair
end AspisR1.AuS1_OnRun
end
