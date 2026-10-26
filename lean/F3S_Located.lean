import F3S_Segments
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_Located
open Aeneas Aeneas.Std Result
variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 theorem singleton (event : S2W_Trace.Event) (pair : GExq_OuterRecord.Event × F3S_Segments.Reads)
    (member : pair ∈ F3S_Segments.one adapter ops stage finish reserved query geo B std hashv event) :
    F3S_Segments.one adapter ops stage finish reserved query geo B std hashv event=[pair] := by
  cases event with
  | returned call value =>
    cases call <;> simp only [F3S_Segments.one,GExq_OuterRecord.project,List.map_nil,List.map_cons,
      List.mem_nil_iff,List.mem_singleton] at member ⊢
    all_goals first | contradiction | (rw [← member])
 theorem on_log (log : S2W_Trace.Log) (pair : GExq_OuterRecord.Event × F3S_Segments.Reads)
    (member : pair ∈ F3S_Segments.all adapter ops stage finish reserved query geo B std hashv log) :
    ∃ event,event ∈ log ∧
      F3S_Segments.one adapter ops stage finish reserved query geo B std hashv event=[pair] := by
  obtain ⟨event,present,member⟩ := List.mem_flatMap.mp member
  exact ⟨event,present,singleton adapter ops stage finish reserved query geo B std hashv event pair member⟩
#print axioms singleton
#print axioms on_log
end AspisR1.F3S_Located
end
