import F3S_FirstPairLog
import F3S_SecondOnRun
import F3S_NativeChildren
import F3S_BatchDictionary
import F3S_Dictionary
import RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_Chronology
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open S2W_NativeConsolidation MultiproofConeCanonical
 theorem log {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (f : FirstCut) (s : SecondCut) (log : S2W_Trace.Log)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s)
    (recorded : RawJ_RecordCuts.Recorded f s saved log)
    (ran : S2W_Trace.run (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (zero : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO
      (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)=ok run.zero)
    (view : Slice U8)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      f.proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok run.root))
    (p2 : AspisR1Stage2.verifier.Prepared) (a2 : AspisR1Stage2.verifier.Accumulator)
    (root2 : Array U8 32#usize) (view2 : Slice U8)
    (reader : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (VTop_Checkpoint.digest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)))
      s.checkpoint s.proof s.pub .S2 ()=ok (.Ok (p2,a2)))
    (range2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      s.proof {start:=7751#usize,«end»:=7783#usize}=ok view2)
    (copy2 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view2=ok (.Ok root2)) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_CallerRecord.code adapter ops (AuS1_Install.base stage) finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot) []).2=
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code (Uni_Install.current ops reserved query geo) B std
        (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std)
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero))) []).2 ++
    (SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv f.proof run.p run.root) []).2 ++
    (SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode run.p
      {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} f.proof f.pub) []).2 ++
    (SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved s.checkpoint s.proof s.pub .S2) []).2 ++
     SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv s.proof p2 root2) []).2))) := by
  let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
    (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
  have binding := S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction
  have extracted : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops (AuS1_Install.base stage) finish reserved query geo B std) native1 native2 hashv := by
    rw [F3S_SdkDictionary.sdk];exact extraction
  have law : S2Z.Oracle.NativeBinding
      (GExq_Caller.sdk adapter ops (AuS1_Install.base stage) finish reserved query geo B std) hashv := by
    rw [F3S_SdkDictionary.sdk];exact binding
  have whole := F3S_NativeChildren.on_pair adapter ops (AuS1_Install.base stage) finish reserved query geo B std
    hashv law native1 native2 extracted id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2 f s log
    (by simpa only [F3S_SdkDictionary.sdk] using ran) recorded
  simp only [F3S_SdkDictionary.sdk] at whole
  have firstNative := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std) D
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success _ f.semantic f.pub f.proof f.split saved cuts.first)
  rw [←GExp_FirstPair.installed ops reserved query geo B std] at firstNative
  have firstSource := (GExq_FirstSource.source (GExp_FirstPair.base ops reserved query geo) B std hashv
    (AspisS6CurrentFirstInstallation.toDigest D) () binding
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split).trans firstNative
  have constants := SdkD_FoldedCut.installed_constants (Uni_Install.current ops reserved query geo) B std
  rw [Uni_Install.compose_tx1] at constants
  have firstLog := F3S_FirstPairLog.log ops reserved query geo B std hashv
    (SdkD_PairBatches.current adapter ops stage finish reserved query geo B std) () binding
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
    (Tx1Q_Execution.actual_slots (Op5T_Concrete.current ops) reserved query geo B std)
    zero constants.1 constants.2 view range copy firstSource
  have secondSource := (GExq_ChildCode.erasure adapter ops (AuS1_Install.base stage) finish reserved query geo
    B std hashv (.op11 D s.pub s.proof s.checkpoint () none) ⟨binding,rfl⟩).trans
    (by simpa only [F3S_SdkDictionary.sdk] using cuts.second)
  have readerSource : erase (SdkC_Source.dictionary hashv) ()
      (GExq_RetainedReader.code reserved s.checkpoint s.proof s.pub .S2)=ok (.Ok (p2,a2)) := by
    rw [GExq_RetainedReader.source reserved hashv D () (binding ())]
    exact reader
  have secondConstants := F3S_Dictionary.second stage finish reserved query geo
  have secondLog := F3S_SecondOnRun.log
    (GExp_SecondPair.base (AuS1_Install.base stage) finish reserved query geo) reserved hashv D
    s.pub s.proof s.checkpoint () p2 a2 root2 view2 readerSource secondConstants.1 secondConstants.2.1
    (secondConstants.2.2 root2) range2 copy2 secondSource
  rw [firstLog,secondLog,F3S_BatchDictionary.current,F3S_BatchDictionary.stage] at whole
  simpa only [List.append_assoc] using whole
#print axioms log
end AspisR1.F3S_Chronology
end
