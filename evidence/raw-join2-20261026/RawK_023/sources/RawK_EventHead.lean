import RawK_ChildHead
import RawK_TraceLogs
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_EventHead
open Aeneas Aeneas.Std Result GExq_OuterLower
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem silent {A : Type} (call : S2W_Trace.Call A) (value : A)
    (empty : GExq_OuterRecord.project call value = []) :
    RawK_TraceLogs.eventLog hashv
      (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
      (.returned call value) = [] := by
  cases call <;> first | rfl | simp only [GExq_OuterRecord.project,List.cons_ne_nil] at empty

theorem marked {A : Type} (call : S2W_Trace.Call A) (value : A)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (first : (GExq_OuterRecord.project call value).head? =
      some (.first semantic pub proof split (.Ok saved)))
    (valid : GExq_ChildCode.Admissible hashv call)
    (returned : S2W_Trace.invoke (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) call = ok value) :
    ∃ entry, (RawK_TraceLogs.eventLog hashv
      (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
      (.returned call value)).head? = some entry ∧ entry.1.head? = some 85 := by
  cases call <;> simp only [GExq_OuterRecord.project,List.head?_nil,List.head?_cons,Option.some.injEq] at first
  case op10 D semantic' pub' proof' split' hash obs =>
    cases first
    obtain ⟨law,rfl⟩ := valid
    exact RawK_ChildHead.first adapter ops stage finish reserved query geo B std hashv
      D semantic' pub' proof' split' hash saved law returned
  case op11 => cases first

#print axioms silent
#print axioms marked
end AspisR1.RawK_EventHead
end
