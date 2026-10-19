import FinishCandidateDotLoopTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FinishRelationCurrent.FinishCandidateDotTrace
private theorem bind_success3 {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem finish_success_trace {W D : Type} (ops : FinishOps W D)
    (fm : Slice U8) (ws : Slice K) (value : E)
    (h : verifier.finish_query_dot ops fm ws = .ok (.Ok value)) :
    ∃ initial final, ops.newDot = .ok initial ∧
      Chain ops fm ws 0#usize initial final ∧ ops.finishDot final = .ok value := by
  unfold verifier.finish_query_dot at h
  obtain ⟨initial,hnew,h⟩ := bind_success3 _ _ _ h
  obtain ⟨out,hloop,h⟩ := bind_success3 _ _ _ h
  rcases out with ⟨final,pending⟩
  have ht := loop_success_trace ops fm ws initial final 0#usize pending (by simp) hloop
  rcases ht with ⟨err,herr⟩ | ⟨hnone,hchain⟩
  · subst pending
    simp at h
  · subst pending
    obtain ⟨result,hfinish,h⟩ := bind_success3 _ _ _ h
    have heq : result = value := by simpa using h
    subst result
    exact ⟨initial,final,hnew,hchain,hfinish⟩

/-- To instantiate a mathematical sum, it suffices to prove one successful
push preserves its prefix invariant. The source loop supplies every read,
weight and successful push witness; those successes are not premises here. -/
theorem chain_invariant {W D : Type} (ops : FinishOps W D)
    (fm : Slice U8) (ws : Slice K) (Inv : Nat → D → Prop)
    (stepLaw : ∀ (j j1 : Usize) (dot dot1 : D) (x : E) (q : K),
      j < ws.len → ops.field fm j = .ok x → Slice.index_usize ws j = .ok q →
      ops.pushDot dot x q = .ok (.Ok (),dot1) →
      (j + 1#usize : Result Usize) = .ok j1 → Inv j.val dot → Inv j1.val dot1)
    {j : Usize} {dot final : D} (trace : Chain ops fm ws j dot final)
    (initial : Inv j.val dot) : Inv ws.len.val final := by
  induction trace with
  | done j dot atEnd => simpa only [atEnd] using initial
  | @step j j1 dot dot1 out x q active read weight push increment tail ih =>
    exact ih (stepLaw j j1 dot dot1 x q active read weight push increment initial)

#print axioms finish_success_trace
#print axioms chain_invariant
end AspisR1FinishRelationCurrent.FinishCandidateDotTrace
