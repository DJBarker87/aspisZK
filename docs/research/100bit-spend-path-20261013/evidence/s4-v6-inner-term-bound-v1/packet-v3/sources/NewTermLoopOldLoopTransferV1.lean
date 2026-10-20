import NewTermBodyOldBodyBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsNewTermLoopOldLoopTransferV1

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

private theorem new_body_done_old_body
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter : Range) (sums out : Array U64 8#usize)
    (hbody : NewBody ops q g slot iter sums = .ok (.done out)) :
    OldBody ops q g slot iter sums = .ok (.done out) := by
  unfold NewBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      have hsum : sums = out := by
        exact ControlFlow.done.inj (Result.ok.inj hrest)
      subst out
      change (do
        let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match o with
        | none => ok (ControlFlow.done sums)
        | some term => do
          let i ← slot * 120#usize
          let i1 ← term * 4#usize
          let i2 ← i + i1
          let i3 ← i + i1
          let i4 ← i3 + 4#usize
          let s ← core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
            { start := i2, «end» := i4 }
          let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
          let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
          let o1 ← ops.m31FromBytes a
          let scalar ← core.option.Option.unwrap o1
          let we ← Array.index_usize g term
          let coefficient ← ops.wideToLimbs we
          let i5 ← ops.wideLimbCount
          let sums1 ← AspisR1FastDotsNewTermBodyOldBodyBridgeV1.OldInnerLoop ops
            { start := 0#usize, «end» := i5 } sums scalar coefficient
          ok (ControlFlow.cont (iter1, sums1))) = .ok (ControlFlow.done sums)
      rw [hnext]
      rfl
  | some _ =>
      repeat' (first | obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest)
      cases Result.ok.inj hrest

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

/-- Success of the v6 term-loop function transfers to the retained old term
    loop, with the exact same output array. This composes the checked v6-body
    bound with the older loop induction used by batch proofs. -/
theorem new_loop_success_old_loop
    (ops : Ops) (q : Array U8 608#usize)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter : Range) (sums out : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hloop : NewLoop ops iter q g slot sums = .ok out) :
    OldLoop ops iter q g slot sums = .ok out := by
  induction hm : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums with
  | h n ih =>
      change Aeneas.Std.loop (newStep ops q g slot) (iter, sums) = .ok out at hloop
      rcases loop_success_cases _ _ _ hloop with hdone | ⟨st', hcont, htail⟩
      · have hnewBody : NewBody ops q g slot iter sums = .ok (.done out) := by
          simpa [newStep] using hdone
        have holdBody := new_body_done_old_body ops q g slot iter sums out hnewBody
        have holdStep : oldStep ops q g slot (iter, sums) = .ok (.done out) := by
          simpa [oldStep] using holdBody
        change Aeneas.Std.loop (oldStep ops q g slot) (iter, sums) = .ok out
        rw [Aeneas.Std.loop.eq_def, holdStep]
      · rcases st' with ⟨iter', sums'⟩
        have hnewBody : NewBody ops q g slot iter sums =
            .ok (.cont (iter', sums')) := by simpa [newStep] using hcont
        have holdBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.new_body_success_old_body
          ops q g slot iter iter' sums sums' hcount hnewBody
        obtain ⟨hlt, hadvance, hend⟩ :=
          AspisR1FastDotsNewTermBodyLinearBoundV1.new_term_body_cont_progress
            ops q g slot iter iter' sums sums' hnewBody
        have hmeasureNext : iter'.end.val - iter'.start.val =
            iter.end.val - iter.start.val - 1 := by
          rw [hend, hadvance]
          omega
        have hdecrease : iter'.end.val - iter'.start.val < n := by
          rw [hmeasureNext, hm]
          omega
        have htail' := ih (iter'.end.val - iter'.start.val) hdecrease iter' sums' htail rfl
        have holdStep : oldStep ops q g slot (iter, sums) =
            .ok (.cont (iter', sums')) := by
          simpa [oldStep] using holdBody
        change Aeneas.Std.loop (oldStep ops q g slot) (iter, sums) = .ok out
        rw [Aeneas.Std.loop.eq_def, holdStep]
        exact htail'

#print axioms new_loop_success_old_loop

end AspisR1FastDotsNewTermLoopOldLoopTransferV1
