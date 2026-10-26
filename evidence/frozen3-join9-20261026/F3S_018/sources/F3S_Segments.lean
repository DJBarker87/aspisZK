import RawK_EventHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_Segments
open Aeneas Aeneas.Std Result GExq_OuterLower
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Reads := List (Bytes × State)
variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def one (event : S2W_Trace.Event) : List (GExq_OuterRecord.Event × Reads) :=
  match event with
  | .returned call value => (GExq_OuterRecord.project call value).map fun mark =>
      (mark,RawK_TraceLogs.eventLog hashv
        (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv) event)

def all (log : S2W_Trace.Log) :=
  log.flatMap (one adapter ops stage finish reserved query geo B std hashv)

theorem projection (log : S2W_Trace.Log) :
    (all adapter ops stage finish reserved query geo B std hashv log).map Prod.fst=
      GExq_RecordTrace.projectLog log := by
  unfold all GExq_RecordTrace.projectLog
  rw [List.map_flatMap]
  congr 1
  funext event
  cases event with
  | returned call value => cases call <;> rfl

theorem chronological (log : S2W_Trace.Log) :
    (all adapter ops stage finish reserved query geo B std hashv log).flatMap Prod.snd=
      RawK_TraceLogs.traceLog hashv
        (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv) log := by
  induction log with
  | nil => rfl
  | cons event tail ih =>
    cases event with
    | returned call value =>
      simp only [all,List.flatMap_cons,List.flatMap_append] at *
      rw [ih]
      cases call <;> simp only [one,GExq_OuterRecord.project,List.map_nil,List.flatMap_nil,
        List.nil_append,List.map_cons,List.flatMap_cons,List.append_nil,RawK_TraceLogs.traceLog,
        List.flatMap_cons]
      all_goals first
        | rfl
        | rw [RawK_EventHead.silent adapter ops stage finish reserved query geo B std hashv _ _ rfl]; rfl

#print axioms projection
#print axioms chronological
end AspisR1.F3S_Segments
end
