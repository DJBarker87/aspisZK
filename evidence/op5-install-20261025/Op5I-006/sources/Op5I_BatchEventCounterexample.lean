import Op5I_AcceptedCarrierCounterexample

set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5I_BatchEventCounterexample
open Aeneas Aeneas.Std Result
open S2W_Trace S2W_ExpandedTrace S2W_ExpandedChildren S2W_TraceSplice
open Op5I_EventCounterexample

/-- The fabricated observation is placed immediately after the actual batch
mark, inside its batch-to-query segment, rather than in an unrelated prefix. -/
def atBatch {E : Type} (read : E) : S2W_ExpandedTrace.Event E → List (S2W_ExpandedTrace.Event E)
  | .site .batch0 => [.site .batch0, .child read]
  | .site .batch1 => [.site .batch1, .child read]
  | event => [event]

def projectedAtBatch {E : Type} (read : E) :
    S2W_SiteSchedule.Event (Option E) → List (S2W_SiteSchedule.Event (Option E))
  | .site .batch0 => [.site .batch0, .source (some read)]
  | .site .batch1 => [.site .batch1, .source (some read)]
  | event => [event]

def inject {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) : ChildConeJoin E ops where
  execute call := do
    let answer ← base.execute call
    ok (answer.1, answer.2.flatMap (atBatch read))
  erasure call := by
    have law := base.erasure call
    cases h : base.execute call <;> simpa [h, S2W_Trace.thenResult] using law

theorem project_one {E : Type} (read : E) (event : S2W_ExpandedTrace.Event E) :
    (atBatch read event).map project = projectedAtBatch read (project event) := by
  cases event with
  | outer event => rfl
  | child event => rfl
  | site site => cases site <;> rfl

theorem project_list {E : Type} (read : E) (events : List (S2W_ExpandedTrace.Event E)) :
    (events.flatMap (atBatch read)).map project =
      (events.map project).flatMap (projectedAtBatch read) := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [List.flatMap_cons, List.map_append, List.map_cons, project_one, ih]

theorem events_injected {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (event : S2W_Trace.Event) :
    events (inject base read) event = (events base event).flatMap (atBatch read) := by
  cases event with
  | returned call value =>
    unfold events
    cases h : base.execute call <;> simp [inject, h]

theorem first_marks {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (original : FirstMarks base) : FirstMarks (inject base read) := by
  constructor
  intro event marked
  obtain ⟨s, layout⟩ := original.source event marked
  let go := fun list => list.flatMap (projectedAtBatch read)
  refine ⟨⟨go s.beforeBatch, .source (some read) :: go s.beforeQuery,
    go s.beforeSave, go s.afterSave⟩, ?_⟩
  rw [events_injected, project_list, layout]
  simp [S2W_SiteSchedule.firstTrace, go, projectedAtBatch, List.append_assoc]

theorem second_marks {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (original : SecondMarks base) : SecondMarks (inject base read) := by
  constructor
  intro event marked
  obtain ⟨s, layout⟩ := original.source event marked
  let go := fun list => list.flatMap (projectedAtBatch read)
  refine ⟨⟨go s.beforeResume, go s.beforeBatch, .source (some read) :: go s.beforeQuery,
    go s.beforeFinish, go s.afterFinish⟩, ?_⟩
  rw [events_injected, project_list, layout]
  simp [S2W_SiteSchedule.secondTrace, go, projectedAtBatch, List.append_assoc]

theorem invocation_unchanged {E : Type} (read : E) (event : S2W_Trace.Event) :
    (invocation (E := E) event).flatMap (atBatch read) = invocation event := by
  cases event with
  | returned call value => cases call <;> rfl

theorem full_injected {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (outer : S2W_Trace.Log) :
    full (children (inject base read)) outer = (full (children base) outer).flatMap (atBatch read) := by
  induction outer with
  | nil => rfl
  | cons event rest ih =>
    simp only [full, List.flatMap_cons, expand, children, events_injected] at *
    rw [List.flatMap_append, List.flatMap_cons, List.flatMap_append, invocation_unchanged]
    change _ = [.outer event] ++ _
    rw [← ih]
    simp only [atBatch, List.singleton_append, List.cons_append, List.append_assoc]

theorem batch_adjacent {E : Type} (read : E) (trace : List (S2W_ExpandedTrace.Event E))
    (site : S2LeadInterface.Site) (batch : site = .batch0 ∨ site = .batch1)
    (member : .site site ∈ trace) :
    ∃ before after, trace.flatMap (atBatch read) = before ++ [.site site, .child read] ++ after := by
  obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
  refine ⟨before.flatMap (atBatch read), after.flatMap (atBatch read), ?_⟩
  rw [same]
  rcases batch with rfl | rfl <;>
    simp [List.flatMap_append, atBatch, List.append_assoc]

#print axioms project_one
#print axioms project_list
#print axioms events_injected
#print axioms first_marks
#print axioms second_marks
#print axioms invocation_unchanged
#print axioms full_injected
#print axioms batch_adjacent
end AspisR1.Op5I_BatchEventCounterexample
end
