import RPz8_RawK_EventHead
import RawK_ModelHead
import RPz8_GExq_EventGood
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_RecordedHead
open Aeneas Aeneas.Std Result GExq_OuterLower

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def Valid (sdk : AdapterRw.Ops) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    S2W_Trace.Event → Prop
  | .returned call value => GExq_ChildCode.Admissible hashv call ∧ S2W_Trace.invoke sdk call = ok value

theorem trace_head (log : S2W_Trace.Log)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (first : (GExq_RecordTrace.projectLog log).head? = some (.first semantic pub proof split (.Ok saved)))
    (valid : ∀ event ∈ log, Valid (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv event) :
    ∃ entry, (RawK_TraceLogs.traceLog hashv
      (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv) log).head? = some entry ∧
      entry.1.head? = some 85 := by
  induction log with
  | nil => cases first
  | cons event tail ih =>
    cases event with
    | returned call value =>
      have current := valid (.returned call value) (List.mem_cons_self ..)
      cases projected : GExq_OuterRecord.project call value with
      | nil =>
        have next : (GExq_RecordTrace.projectLog tail).head? =
            some (.first semantic pub proof split (.Ok saved)) := by
          simpa only [GExq_RecordTrace.projectLog,List.flatMap_cons,projected,List.nil_append] using first
        obtain ⟨entry,h,tag⟩ := ih next (fun e he => valid e (List.mem_cons_of_mem _ he))
        refine ⟨entry,?_,tag⟩
        simpa only [RawK_TraceLogs.traceLog,List.flatMap_cons,
          RawK_EventHead.silent adapter ops stage finish reserved query geo B std hashv call value projected,
          List.nil_append] using h
      | cons mark rest =>
        have same : mark = .first semantic pub proof split (.Ok saved) := by
          simpa only [GExq_RecordTrace.projectLog,List.flatMap_cons,projected,List.cons_append,
            List.head?_cons,Option.some.injEq] using first
        have marker : (GExq_OuterRecord.project call value).head? =
            some (.first semantic pub proof split (.Ok saved)) := by rw [projected,same]; rfl
        obtain ⟨entry,h,tag⟩ := RawK_EventHead.marked adapter ops stage finish reserved query geo B std hashv
          call value semantic pub proof split saved marker current.1 current.2
        refine ⟨entry,?_,tag⟩
        exact RawK_ModelHead.append_head _ _ entry h

#print axioms trace_head
end AspisR1.RawK_RecordedHead
end
