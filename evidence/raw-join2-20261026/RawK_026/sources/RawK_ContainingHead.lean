import RawK_RecordedHead
import RawJ_RecordCuts
import GExq_OuterGoodTwo
import GExq_CallerRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_ContainingHead
open Aeneas Aeneas.Std Result GExq_OuterLower

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first (law : S2Z.Oracle.NativeBinding
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut) (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log))
    (recorded : RawJ_RecordCuts.Recorded f s saved log) :
    ∃ entry, (SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_CallerRecord.code adapter ops stage finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot) []).2).head? = some entry ∧
      entry.1.head? = some 85 := by
  let sdk := GExq_Caller.sdk adapter ops stage finish reserved query geo B std
  let code := S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot
  let impl := @GExq_Caller.child F C adapter ops stage finish reserved query geo B std hashv
  have good := GExq_OuterGoodTwo.two sdk hashv law id accounts1 accounts2 data1 data2 slot
  have valid : ∀ event ∈ log, RawK_RecordedHead.Valid sdk hashv event := by
    intro event member
    cases event with
    | returned call value =>
      exact ⟨GExq_EventGood.on_run sdk hashv code good [] log (.Ok saved) (by simp) ran _ member,
        S2W_TraceFacts.run_valid sdk code [] log (.Ok saved) (by simp) ran _ member⟩
  have firstMark : (GExq_RecordTrace.projectLog log).head? =
      some (.first f.semantic f.pub f.proof f.split (.Ok saved)) := by rw [recorded.2]; rfl
  obtain ⟨entry,h,tag⟩ := RawK_RecordedHead.trace_head adapter ops stage finish reserved query geo B std hashv
    log f.semantic f.pub f.proof f.split saved firstMark valid
  have ordered := RawK_TraceLogs.ordered sdk hashv impl
    (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv)
    code good [] log (.Ok saved) ran
  simp only [RawK_TraceLogs.traceLog,List.flatMap_nil,List.nil_append] at ordered
  refine ⟨entry,?_,tag⟩
  unfold GExq_CallerRecord.code
  rw [GExq_RecordLog.log]
  exact (congrArg List.head? ordered).symm.trans h

#print axioms first
end AspisR1.RawK_ContainingHead
end
