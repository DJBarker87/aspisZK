import PV_RJ4IDB_OpenInputs
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
/-! Local source-observer recurrences. These links describe initialization,
per-event accumulation and readout separately. They are not native instances.
EventOrder must include every emitted prefix, including abnormal paths. -/
def PV_DIAG10_Link_Init {I X : Type} (state : I → List NativeEvent → X)
 (zero : X) : Prop := ∀ i, state i [] = zero
def PV_DIAG10_Link_Step {I X : Type} (state : I → List NativeEvent → X)
 (join : X → X → X) (single : NativeEvent → X) : Prop :=
 ∀ i es e, state i (es ++ [e]) = join (state i es) (single e)
def PV_DIAG10_Link_Readout {I X : Type} (actual : I → X)
 (state : I → List NativeEvent → X) (raw : I → List NativeEvent) : Prop :=
 ∀ i, actual i = state i (raw i)
def PV_DIAG10_Link_EventOrder {I A : Type} (raw : I → List NativeEvent)
 (native : I → NativeTrace A) : Prop := ∀ i, (native i).events = raw i

theorem prefix_agreement {I X : Type} (state : I → List NativeEvent → X)
 (project : List NativeEvent → X) (join : X → X → X)
 (initial : PV_DIAG10_Link_Init state (project []))
 (step : PV_DIAG10_Link_Step state join (fun e => project [e]))
 (projectStep : ∀ es e, project (es++[e])=join (project es) (project [e]))
 (i : I) (es : List NativeEvent) : state i es = project es := by
 have aux : ∀ tail head, state i head = project head →
     state i (head++tail) = project (head++tail) := by
   intro tail
   induction tail with
   | nil => intro head h; simpa only [List.append_nil] using h
   | cons e tail ih =>
     intro head h
     have hnext : state i (head++[e])=project (head++[e]) := by
       rw [step,projectStep,h]
     simpa only [List.append_assoc,List.cons_append,List.nil_append] using
       ih (head++[e]) hnext
 simpa only [List.nil_append] using aux es [] (initial i)
#print axioms prefix_agreement
end PV_DIAG10
