import S2W_ExpandedChildren
import S2W_FirstOccurrence

/-! Full native outer trace occurrence selection and child substitution.
Only local source-mark layouts are supplied by the two child cones. -/
set_option autoImplicit false
namespace AspisR1.S2W_TraceSplice
open Aeneas Aeneas.Std Result S2W_Trace S2W_OuterOccurrences S2W_ExpandedTrace S2W_ExpandedChildren

theorem run_shift (ops : AdapterRw.Ops) {A : Type} (code : Code A) (headLog log : Log) :
    run ops code (headLog ++ log) = thenResult (run ops code log)
      (fun answer => ok (answer.1,headLog ++ answer.2)) := by
  induction code generalizing log with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok b => exact ih b log
  | call call k ih =>
    cases invoked : invoke ops call with
    | fail e => simp only [run,invoked,thenResult]
    | div => simp only [run,invoked,thenResult]
    | ok b => simpa only [run,invoked,thenResult,List.append_assoc] using
        ih b (log ++ [.returned call b])

/-- Select a real occurrence from the log; headLog/suffix are computed by list
induction. The same typed event, including arguments and result, is retained. -/
theorem split_tag (log : Log) (tag : Bool) (rest : List Bool)
    (shape : tags log = tag :: rest) :
    ∃ pre event post, log = pre ++ event :: post ∧ tags pre = [] ∧
      mark event = some tag ∧ tags post = rest := by
  induction log with
  | nil => cases shape
  | cons event tail ih =>
    cases marked : mark event with
    | none =>
      have next : tags tail = tag :: rest := by simpa [tags,marked] using shape
      obtain ⟨pre,chosen,post,same,empty,first,last⟩ := ih next
      exact ⟨event :: pre,chosen,post,by simp [same],by simp [tags,marked] at empty ⊢; exact empty,first,last⟩
    | some value =>
      have next : value :: tags tail = tag :: rest := by simpa [tags,marked] using shape
      have same := List.cons.inj next
      exact ⟨[],event,tail,rfl,rfl,same.1 ▸ marked,same.2⟩

def project {E : Type} : S2W_ExpandedTrace.Event E → S2W_SiteSchedule.Event (Option E)
  | .outer _ => .source none
  | .child event => .source (some event)
  | .site site => .site site

def projected {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops) (log : Log) :=
  (full (children port) log).map project

/-- Independently named CHILD layout theorems about their own source runs.
No full caller schedule, account observation, input identity or caller field. -/
structure FirstMarks {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops) : Prop where
  source : ∀ event, mark event = some false → ∃ fs : S2W_SiteSchedule.FirstSegments (Option E),
    (events port event).map project = S2W_SiteSchedule.firstTrace fs
structure SecondMarks {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops) : Prop where
  source : ∀ event, mark event = some true → ∃ ss : S2W_SiteSchedule.SecondSegments (Option E),
    (events port event).map project = S2W_SiteSchedule.secondTrace ss

theorem invocation_first {E : Type} (event : S2W_Trace.Event) (marked : mark event = some false) :
    invocation (E := E) event = [.site .tx1] := by
  cases event with
  | returned call value => cases call <;> simp_all [mark,invocation]
theorem invocation_second {E : Type} (event : S2W_Trace.Event) (marked : mark event = some true) :
    invocation (E := E) event = [.site .tx2] := by
  cases event with
  | returned call value => cases call <;> simp_all [mark,invocation]

/-- The schedule is a projection of the expanded outer log, including the
post-TX2 outer suffix. Prefix/middle are DERIVED occurrence segments. -/
theorem expanded_schedule {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops)
    (first : FirstMarks port) (second : SecondMarks port) (outer : Log)
    (shape : tags outer = [false,true]) :
    ∃ pre middle fs ss,
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss := by
  obtain ⟨pre,e1,rest,same,_,m1,remaining⟩ := split_tag outer false [true] shape
  obtain ⟨middle,e2,post,same2,_,m2,_⟩ := split_tag rest true [] remaining
  obtain ⟨fs,layout1⟩ := first.source e1 m1
  obtain ⟨ss,layout2⟩ := second.source e2 m2
  let headLog := projected port pre ++ [.source none]
  let interval := projected port middle ++ [.source none]
  let ss' := {ss with afterFinish := ss.afterFinish ++ projected port post}
  refine ⟨headLog,interval,fs,ss',?_⟩
  have splice := S2W_ExpandedTrace.splice (children port) outer pre middle post e1 e2
    (by simp only [same,same2,List.append_assoc,List.cons_append,List.nil_append])
  unfold projected
  rw [splice]
  simp only [List.map_append,expand,children,invocation_first e1 m1,invocation_second e2 m2,
    List.map_cons,List.map_nil,project,layout1,layout2]
  simp only [headLog,interval,ss',S2W_SiteSchedule.timeline,S2W_SiteSchedule.secondTrace,
    projected,List.append_assoc,List.cons_append,List.nil_append]

#print axioms run_shift
#print axioms split_tag
#print axioms invocation_first
#print axioms invocation_second
#print axioms expanded_schedule
#print FirstMarks
#print SecondMarks
end AspisR1.S2W_TraceSplice
