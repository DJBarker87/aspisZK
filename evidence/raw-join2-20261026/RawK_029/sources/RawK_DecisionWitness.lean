import RawK_ContainingHead
import RawK_ModelAll
import RawJ_OriginalAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_DecisionWitness
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

/-- Position zero is already different. The source world is the same H, and
f/s are the recorded original caller cuts. Every model transcript is covered,
so this includes the model transcript selected from those same cuts. No model
acceptance, parser, query or no-collision premise is added. -/
theorem first_difference
    (law : S2Z.Oracle.NativeBinding (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut) (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log))
    (recorded : RawJ_RecordCuts.Recorded f s saved log) :
    ∃ sourceEntry,
      (eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot)).1.head? = some sourceEntry ∧
      sourceEntry.1.head? = some 85 ∧
      ∀ (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage),
        (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.head? ≠ some sourceEntry ∧
        (eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
          id accounts1 accounts2 data1 data2 slot)).1 ≠
          (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1 := by
  obtain ⟨entry,h,tag⟩ := RawK_ContainingHead.first adapter ops stage finish reserved query geo B std hashv
    law id accounts1 accounts2 data1 data2 slot saved f s log ran recorded
  have exactRun := RawJ_OriginalAccepted.accepted adapter ops stage finish reserved query geo B std hashv
    law sha256 H p1 syscall id accounts1 accounts2 data1 data2 slot saved f s log ran recorded
  have sourceHead : (eval H (GExq_CallerRecord.program adapter ops stage finish reserved query geo B std hashv
      id accounts1 accounts2 data1 data2 slot)).1.head? = some entry := by rw [exactRun]; exact h
  refine ⟨entry,sourceHead,tag,?_⟩
  intro stored tr m
  have diff := RawK_ModelAll.different H stored tr m entry tag
  refine ⟨diff,?_⟩
  intro equal
  exact diff ((congrArg List.head? equal).symm.trans sourceHead)

#print axioms first_difference
#print first_difference
end AspisR1.RawK_DecisionWitness
end
