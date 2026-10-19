import QueryTailBodySuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2QueryTailCut.QueryTailProof
private theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧ Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext,rfl,h⟩

inductive Chain (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry) :
    verifier.Accumulator → verifier.BatchedWeights →
    verifier.Accumulator → verifier.BatchedWeights → Nat → Prop
  | done (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
      (atEnd : a.next.val = 22) : Chain query proof p g obs geometry a pending a pending 0
  | step {a a1 out : verifier.Accumulator} {pending pendingOut : verifier.BatchedWeights}
      {o : Option verifier.BatchedWeights} {n : Nat}
      (active : a.next < 22#usize)
      (call : query proof p a g obs geometry (some pending) = .ok (.Ok (),a1,o))
      (tail : Chain query proof p g obs geometry a1 (retained pending o) out pendingOut n) :
      Chain query proof p g obs geometry a pending out pendingOut (n+1)

theorem loop_success_trace (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (advance : ∀ (a a1 : verifier.Accumulator) (pending : verifier.BatchedWeights)
      (o : Option verifier.BatchedWeights),
      query proof p a g obs geometry (some pending) = .ok (.Ok (),a1,o) →
      a1.next.val = a.next.val + 1)
    (a out : verifier.Accumulator) (pending pendingOut : verifier.BatchedWeights)
    (ret : Option (core.result.Result
      (verifier.Prepared × verifier.Accumulator × verifier.BatchedWeights) verifier.Error))
    (ha : a.next.val ≤ 22)
    (hrun : verifier.candidate.tx2_query_tail_loop query proof p a g obs geometry pending =
      .ok (out,pendingOut,ret)) :
    (∃ e, ret = some (.Err e)) ∨
    (ret = none ∧ Chain query proof p g obs geometry a pending out pendingOut (22-a.next.val)) := by
  let step := fun s : verifier.Accumulator × verifier.BatchedWeights =>
    verifier.candidate.tx2_query_tail_loop.body query proof p g obs geometry s.1 s.2
  have hloop : Aeneas.Std.loop step (a,pending) = .ok (out,pendingOut,ret) := hrun
  induction hfuel : 22 - a.next.val generalizing a out pending pendingOut ret with
  | zero =>
    have heq : a.next.val = 22 := by omega
    rcases loop_success_cases step (a,pending) (out,pendingOut,ret) hloop with hdone | ⟨s,hcont,htail⟩
    · cases ret with
      | none =>
        obtain ⟨_,hout,hpending⟩ := body_done_none query proof p g obs geometry a out pending pendingOut hdone
        subst out; subst pendingOut
        exact Or.inr ⟨rfl,Chain.done a pending heq⟩
      | some r =>
        cases r with
        | Err e => exact Or.inl ⟨e,rfl⟩
        | Ok value => exact (body_done_not_ok query proof p g obs geometry a out pending pendingOut value hdone).elim
    · rcases s with ⟨a1,pending1⟩
      have hc := body_cont query proof p g obs geometry a a1 pending pending1 hcont
      have hlt : a.next.val < 22 := hc.1
      omega
  | succ fuel ih =>
    rcases loop_success_cases step (a,pending) (out,pendingOut,ret) hloop with hdone | ⟨s,hcont,htail⟩
    · cases ret with
      | none =>
        have hd := body_done_none query proof p g obs geometry a out pending pendingOut hdone
        have hn : ¬a.next.val < 22 := hd.1
        omega
      | some r =>
        cases r with
        | Err e => exact Or.inl ⟨e,rfl⟩
        | Ok value => exact (body_done_not_ok query proof p g obs geometry a out pending pendingOut value hdone).elim
    · rcases s with ⟨a1,pending1⟩
      obtain ⟨hactive,o,hquery,hpending⟩ := body_cont query proof p g obs geometry a a1 pending pending1 hcont
      have hval := advance a a1 pending o hquery
      have hactiveN : a.next.val < 22 := hactive
      have hnext : a1.next.val ≤ 22 := by omega
      have hfnext : 22 - a1.next.val = fuel := by omega
      have hrunNext : verifier.candidate.tx2_query_tail_loop query proof p a1 g obs geometry pending1 =
        .ok (out,pendingOut,ret) := htail
      have ht := ih a1 out pending1 pendingOut ret hnext hrunNext htail hfnext
      rcases ht with herr | ⟨hnone,hchain⟩
      · exact Or.inl herr
      · subst pending1
        exact Or.inr ⟨hnone,Chain.step hactive hquery hchain⟩

theorem chain_end (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    {a out : verifier.Accumulator} {pending pendingOut : verifier.BatchedWeights} {n : Nat}
    (h : Chain query proof p g obs geometry a pending out pendingOut n) :
    out.next.val = 22 := by
  induction h with
  | done a pending heq => exact heq
  | step active call tail ih => exact ih
#print axioms loop_success_trace
#print axioms chain_end
end AspisR1Stage2QueryTailCut.QueryTailProof
