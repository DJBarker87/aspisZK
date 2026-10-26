import RPz7_SInt2_AcceptedPairClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5I_EventCounterexample
open Aeneas Aeneas.Std Result
open S2W_Trace S2W_ExpandedTrace S2W_ExpandedChildren S2W_TraceSplice
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

abbrev ReadEvent := Bytes × State

/-- A countermodel of the retained event contract, not a source implementation.
All original values and error/divergence outcomes are preserved. -/
def inject {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) : ChildConeJoin E ops where
  execute call := do
    let answer ← base.execute call
    ok (answer.1, .child read :: answer.2)
  erasure call := by
    have law := base.erasure call
    cases h : base.execute call <;> simpa [h, S2W_Trace.thenResult] using law

/-- On every actually returning child, the contract permits an arbitrary
additional event, without executing a different source call. -/
theorem returned {E A : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (call : Call A) (value : A) (accepted : invoke ops call = ok value) :
    (inject base read).execute call = ok (value, .child read :: events base (.returned call value)) := by
  simp only [inject, returned_child base call value accepted, bind_tc_ok]

theorem event_nonempty {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (event : S2W_Trace.Event) (nonempty : events base event ≠ []) :
    events (inject base read) event = .child read :: events base event := by
  cases event with
  | returned call value =>
    unfold events at nonempty ⊢
    cases h : base.execute call <;> simp [h] at nonempty
    simp [inject, h]

theorem first_marks {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (original : FirstMarks base) : FirstMarks (inject base read) := by
  constructor
  intro event marked
  obtain ⟨segments, layout⟩ := original.source event marked
  have nonempty : events base event ≠ [] := by
    intro empty
    rw [empty] at layout
    have lengths := congrArg List.length layout
    simp [S2W_SiteSchedule.firstTrace] at lengths
  refine ⟨{segments with beforeBatch := .source (some read) :: segments.beforeBatch}, ?_⟩
  rw [event_nonempty base read event nonempty]
  simpa only [List.map_cons, project, S2W_SiteSchedule.firstTrace, List.cons_append]
    using congrArg (List.cons (.source (some read))) layout

theorem second_marks {E : Type} {ops : AdapterRw.Ops} (base : ChildConeJoin E ops)
    (read : E) (original : SecondMarks base) : SecondMarks (inject base read) := by
  constructor
  intro event marked
  obtain ⟨segments, layout⟩ := original.source event marked
  have nonempty : events base event ≠ [] := by
    intro empty
    rw [empty] at layout
    have lengths := congrArg List.length layout
    simp [S2W_SiteSchedule.secondTrace] at lengths
  refine ⟨{segments with beforeResume := .source (some read) :: segments.beforeResume}, ?_⟩
  rw [event_nonempty base read event nonempty]
  simpa only [List.map_cons, project, S2W_SiteSchedule.secondTrace, List.cons_append]
    using congrArg (List.cons (.source (some read))) layout

#print axioms returned
#print axioms event_nonempty
#print axioms first_marks
#print axioms second_marks
end AspisR1.Op5I_EventCounterexample
end
