from pathlib import Path
import json
D=Path(__file__).parent
plans={}
head='import PV_RJ4IDB_OpenInputs\nset_option autoImplicit false\nnamespace PV_DIAG10\nopen PV_RJ4IDB\n'
base=head+'''/-! Local source-observer recurrences. These links describe initialization,
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
'''
plans['PV_DIAG10_Links']=[base+'end PV_DIAG10\n']
for tag,typ,proj,join,defs in [
 ('FILE','List FileOp','nativeFiles','List.append','nativeFiles'),
 ('JSON_STDOUT','List Bytes × List (Bytes × Bytes)','(fun es => (nativeJSON es,nativeStdout es))','(fun a b => (a.1++b.1,a.2++b.2))','nativeJSON,nativeStdout'),
 ('ERROR_STDERR','List PV_DIAG2.Effect × List PV_DIAG3.Event','(fun es => (nativeDiag2 es,nativeDiag3 es))','(fun a b => (a.1++b.1,a.2++b.2))','nativeDiag2,nativeDiag3')]:
 src='import PV_DIAG10_Links\nset_option autoImplicit false\nnamespace PV_DIAG10\nopen PV_RJ4IDB\n'
 src+=f'''theorem DIAG_{tag}_TRACE {{I A : Type}} (actual : I → {typ})
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (state : I → List NativeEvent → {typ})
 (initial : PV_DIAG10_Link_Init state ({proj} []))
 (step : PV_DIAG10_Link_Step state {join} (fun e => {proj} [e]))
 (readout : PV_DIAG10_Link_Readout actual state raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.DIAG_{tag}_TRACE actual native := by
 intro i
 rw [readout i,order i]
 apply prefix_agreement state {proj} {join} initial step
 intro es e
 simp only [{defs},List.filterMap_append] <;> rfl
#print axioms DIAG_{tag}_TRACE
end PV_DIAG10
'''
 plans['PV_DIAG10_'+tag]=[src]
for m,cs in plans.items():(D/(m+'.lean')).write_text(cs[-1])
(D/'skeleton-plans.json').write_text(json.dumps(plans,indent=2)+'\n')
