import NewTermBodyOldBodyBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsReverseTermLoopRootV1

abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Range := core.ops.range.Range Usize
abbrev Ops := AspisR1FastDotsNewTermBodyLinearBoundV1.Ops
abbrev NewBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.NewBody
abbrev OldBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.OldBody
abbrev NewLoop := AspisR1FastDotsNewTermBodyLinearBoundV1.NewTermLoop
abbrev OldLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok flow =>
      cases flow with
      | done result =>
          simp only [hs, bind_tc_ok] at h
          have heq : result = out := Result.ok.inj h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp only [hs, bind_tc_ok] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

private def newStep (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) : (Range × Array U64 8#usize) →
      Result (ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize)) :=
  fun s => NewBody ops q g slot s.1 s.2

private def oldStep (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) : (Range × Array U64 8#usize) →
      Result (ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize)) :=
  fun s => OldBody ops q g slot s.1 s.2

/-- Lift a successful old term-body to fixed-body law through the complete
original term loop. Progress is obtained from the same transported body,
not assumed as a separate termination oracle. -/
theorem old_term_loop_success_fixed_term_loop
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter : Range) (sums out : Array U64 8#usize)
    (hbodyLaw : ∀ (cursor : Range) (state : Array U64 8#usize)
      (flow : ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize)),
      OldBody ops q g slot cursor state = .ok flow →
      NewBody ops q g slot cursor state = .ok flow)
    (hloop : OldLoop ops iter q g slot sums = .ok out) :
    NewLoop ops iter q g slot sums = .ok out := by
  induction hm : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums with
  | h n ih =>
      change Aeneas.Std.loop (oldStep ops q g slot) (iter, sums) = .ok out at hloop
      rcases loop_success_cases _ _ _ hloop with hdone | ⟨st', hcont, htail⟩
      · have hnewBody : OldBody ops q g slot iter sums = .ok (.done out) := by
          simpa [oldStep] using hdone
        have holdBody := hbodyLaw iter sums (.done out) hnewBody
        have hnewStep : newStep ops q g slot (iter, sums) = .ok (.done out) := by
          simpa [newStep] using holdBody
        change Aeneas.Std.loop (newStep ops q g slot) (iter, sums) = .ok out
        rw [Aeneas.Std.loop.eq_def, hnewStep]
      · rcases st' with ⟨iter', sums'⟩
        have hnewBody : OldBody ops q g slot iter sums =
            .ok (.cont (iter', sums')) := by simpa [oldStep] using hcont
        have holdBody := AspisR1FastDotsNewTermBodyNewBodyBridgeV1.new_body_success_old_body
          ops q g slot iter iter' sums sums' hcount hnewBody
        obtain ⟨hlt, hadvance, hend⟩ :=
          AspisR1FastDotsNewTermBodyLinearBoundV1.new_term_body_cont_progress
            ops q g slot iter iter' sums sums' holdBody
        have hmeasureNext : iter'.end.val - iter'.start.val =
            iter.end.val - iter.start.val - 1 := by
          rw [hend, hadvance]
          omega
        have hdecrease : iter'.end.val - iter'.start.val < n := by
          rw [hmeasureNext, hm]
          omega
        have htail' := ih (iter'.end.val - iter'.start.val) hdecrease iter' sums' htail rfl
        have hnewStep : newStep ops q g slot (iter, sums) =
            .ok (.cont (iter', sums')) := by
          simpa [newStep] using holdBody
        change Aeneas.Std.loop (newStep ops q g slot) (iter, sums) = .ok out
        rw [Aeneas.Std.loop.eq_def, hnewStep]
        exact htail'


#print axioms old_term_loop_success_fixed_term_loop
end AspisR1FastDotsReverseTermLoopRootV1
