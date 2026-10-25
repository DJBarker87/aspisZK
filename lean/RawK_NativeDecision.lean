import RawK_DecisionWitness
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_NativeDecision
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

/-- The obstruction is derived from the two original accepted submissions.
Cuts and their containing log are outputs, never independent accepting-log
hypotheses. The quantified model inputs include every same-cut construction. -/
theorem accepted_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot = ok (.Ok ())) :
    let sdk := GExq_Caller.sdk adapter ops stage finish reserved query geo B std
    ∃ f s log,
      S2W_NativeConsolidation.SourceCuts sdk accounts1 accounts2 saved f s ∧
      RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run sdk (S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,log) ∧
      ∃ sourceEntry,
        (eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
          id accounts1 accounts2 data1 data2 slot)).1.head? = some sourceEntry ∧
        sourceEntry.1.head? = some 85 ∧
        ∀ (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage),
          (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.head? ≠ some sourceEntry ∧
          (eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
            id accounts1 accounts2 data1 data2 slot)).1 ≠
            (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1 := by
  obtain ⟨f,s,log,cuts,recorded,ran⟩ := RawJ_RecordCuts.native
    (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
    native1 native2 hashv extraction id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  refine ⟨f,s,log,cuts,recorded,ran,?_⟩
  exact RawK_DecisionWitness.first_difference adapter ops stage finish reserved query geo B std hashv
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction)
    sha256 H p1 syscall id accounts1 accounts2 data1 data2 slot saved f s log ran recorded

#print axioms accepted_pair
#print accepted_pair
end AspisR1.RawK_NativeDecision
end
