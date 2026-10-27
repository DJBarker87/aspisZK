import RPz7_F3N_ConsSource
import RPz7_PAln_Oracle
import RPz7_RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SameRun
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation MultiproofConeCanonical

theorem accepted {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words) :
    ∃ f s log,
      SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
        accounts1 accounts2 saved f s ∧ RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
        (S2W_Observation.two (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
          id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log) ∧
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (SdkD_PairBatches.current a ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ (view : Slice U8) (i : F3_Model.Input),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok run.root) ∧
      F3N_SourceInput.Facts f run.p H i := by
  obtain ⟨f,s,log,cuts,recorded,ran⟩ := RawJ_RecordCuts.native _ native1 native2 hashv extraction
    id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  obtain ⟨run,view,range,copy⟩ := SdkD_PairBatches.first_run a ops stage finish reserved query geo B std
    accounts1 accounts2 saved f s cuts
  have extracted : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps (F3N_ConsDictionary.adapter a stage finish reserved query geo)
        (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std)
      native1 native2 hashv := by rw [← F3N_ConsDictionary.dictionary];exact extraction
  have backend := PAln_Oracle.installed_backend (F3N_ConsDictionary.adapter a stage finish reserved query geo)
    (Op5T_Concrete.current ops) reserved query geo B std native1 native2 hashv extracted sha256 H p1 syscall
  obtain ⟨i,facts⟩ := F3N_ConsSource.from_cut a ops stage finish reserved query geo B std accounts1 accounts2
    saved f s cuts recorded.1 run H backend w
  exact ⟨f,s,log,cuts,recorded,ran,run,view,i,range,copy,facts⟩

#print axioms accepted
end AspisR1.F3N_SameRun
end
