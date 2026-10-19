import FinishCandidateDotTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1FinishRelationCurrent.FinishCandidateDotTrace
private theorem bind_success2 {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
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

theorem body_done_not_ok {W D : Type} (ops : FinishOps W D)
    (fm : Slice U8) (ws : Slice K) (dot dot1 : D) (j : Usize) (out : E)
    (h : verifier.finish_query_dot_loop.body ops fm ws dot j =
      .ok (.done (dot1,some (.Ok out)))) : False := by
  unfold verifier.finish_query_dot_loop.body at h
  by_cases hj : j < ws.len
  · simp only [Slice.len, hj, ↓reduceIte] at h
    obtain ⟨x,hx,h⟩ := bind_success2 _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success2 _ _ _ h
    obtain ⟨pair,hp,h⟩ := bind_success2 _ _ _ h
    rcases pair with ⟨r,d⟩
    cases r with
    | Err err =>
      cases err
      simp [core.result.Result.map_err,
        verifier.finish_query_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok u =>
      cases u
      change (do let n ← (j + 1#usize : Result Usize)
                 .ok (ControlFlow.cont (β := D × Option (core.result.Result E verifier.Error)) (d,n))) =
          .ok (ControlFlow.done (dot1,some (.Ok out))) at h
      obtain ⟨n,hn,h⟩ := bind_success2 _ _ _ h
      simp at h
  · simp [Slice.len,hj] at h

inductive Chain {W D : Type} (ops : FinishOps W D) (fm : Slice U8) (ws : Slice K) :
    Usize → D → D → Prop
  | done (j : Usize) (dot : D) (atEnd : j.val = ws.len.val) : Chain ops fm ws j dot dot
  | step {j j1 : Usize} {dot dot1 out : D} (x : E) (q : K)
      (active : j < ws.len) (read : ops.field fm j = .ok x)
      (weight : Slice.index_usize ws j = .ok q)
      (push : ops.pushDot dot x q = .ok (.Ok (),dot1))
      (increment : (j + 1#usize : Result Usize) = .ok j1)
      (tail : Chain ops fm ws j1 dot1 out) : Chain ops fm ws j dot out

private theorem increment_val (j j1 : Usize) {n : Nat} (hj : j.val < n)
    (cap : n ≤ Usize.max) (h : (j + 1#usize : Result Usize) = .ok j1) :
    j1.val = j.val + 1 := by
  have spec : UScalar.add j 1#usize ⦃r => r.val = j.val + 1⦄ := by
    apply UScalar.add_spec
    have hroom : j.val + (1#usize).val ≤ Usize.max := by simpa using (show j.val + 1 ≤ Usize.max by omega)
    simpa only [UScalar.max_USize_eq] using hroom
  obtain ⟨r,hr,hval⟩ := WP.spec_imp_exists spec
  have : r = j1 := Result.ok.inj (hr.symm.trans h)
  simpa [this] using hval

theorem loop_success_trace {W D : Type} (ops : FinishOps W D)
    (fm : Slice U8) (ws : Slice K) (dot out : D) (j : Usize)
    (pending : Option (core.result.Result E verifier.Error))
    (hj : j.val ≤ ws.len.val)
    (hrun : verifier.finish_query_dot_loop ops fm ws dot j = .ok (out,pending)) :
    (∃ err, pending = some (.Err err)) ∨
      (pending = none ∧ Chain ops fm ws j dot out) := by
  let step := fun s : D × Usize => verifier.finish_query_dot_loop.body ops fm ws s.1 s.2
  have hloop : Aeneas.Std.loop step (dot,j) = .ok (out,pending) := hrun
  induction hfuel : ws.len.val - j.val generalizing dot out j pending with
  | zero =>
    have heq : j.val = ws.len.val := by omega
    rcases loop_success_cases step (dot,j) (out,pending) hloop with hdone | ⟨s,hcont,htail⟩
    · cases pending with
      | none =>
        have hd := body_done_none ops fm ws dot out j hdone
        have he : out = dot := hd.2
        subst out
        exact Or.inr ⟨rfl, Chain.done j dot heq⟩
      | some r =>
        cases r with
        | Err err => exact Or.inl ⟨err,rfl⟩
        | Ok x => exact (body_done_not_ok ops fm ws dot out j x hdone).elim
    · obtain ⟨d1,j1⟩ := s
      have hc := body_cont ops fm ws dot d1 j j1 hcont
      have hlt : j.val < ws.len.val := hc.1
      omega
  | succ fuel ih =>
    rcases loop_success_cases step (dot,j) (out,pending) hloop with hdone | ⟨s,hcont,htail⟩
    · cases pending with
      | none =>
        have hd := body_done_none ops fm ws dot out j hdone
        have : ¬j.val < ws.len.val := hd.1
        omega
      | some r =>
        cases r with
        | Err err => exact Or.inl ⟨err,rfl⟩
        | Ok x => exact (body_done_not_ok ops fm ws dot out j x hdone).elim
    · rcases s with ⟨d1,j1⟩
      obtain ⟨hactive,x,q,hread,hw,hpush,hinc⟩ := body_cont ops fm ws dot d1 j j1 hcont
      have hactiveN : j.val < ws.len.val := hactive
      have hval := increment_val j j1 hactiveN ws.property hinc
      have hnext : j1.val ≤ ws.len.val := by omega
      have hfnext : ws.len.val - j1.val = fuel := by omega
      have hrunNext : verifier.finish_query_dot_loop ops fm ws d1 j1 = .ok (out,pending) := htail
      have hnextTrace := ih d1 out j1 pending hnext hrunNext htail hfnext
      rcases hnextTrace with herror | ⟨hnone,hchain⟩
      · exact Or.inl herror
      · exact Or.inr ⟨hnone,Chain.step x q hactive hread hw hpush hinc hchain⟩
#print axioms body_done_not_ok
#print axioms increment_val
#print axioms loop_success_trace
end AspisR1FinishRelationCurrent.FinishCandidateDotTrace
