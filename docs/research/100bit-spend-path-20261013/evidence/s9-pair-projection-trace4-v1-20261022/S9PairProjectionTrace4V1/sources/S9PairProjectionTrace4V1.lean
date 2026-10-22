import S9PairProjectionDotAtV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1S9PairProjectionTrace4V1
open AspisR1S9PairCallerStepV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (7#usize)

def range0 : R := { start := 0#usize, «end» := 4#usize }
def range1 : R := { start := 1#usize, «end» := 4#usize }
def range2 : R := { start := 2#usize, «end» := 4#usize }
def range3 : R := { start := 3#usize, «end» := 4#usize }
def range4 : R := { start := 4#usize, «end» := 4#usize }

def projectionBody (f : Slice U8) (libra : Array field.WideExact (4#usize)) :
    R × W → Result (ControlFlow (R × W) W) := fun s =>
  weights.Weights.pair_s2_libra_parts_projection_loop.body f libra s.1 s.2

def projectionLoop (f : Slice U8) (libra : Array field.WideExact (4#usize))
    (initial : W) : Result W :=
  weights.Weights.pair_s2_libra_parts_projection_loop range0 f initial libra

private theorem range_eq (r s : R)
    (hs : r.start = s.start) (he : r.end = s.end) : r = s := by
  cases r
  cases s
  cases hs
  cases he
  rfl

theorem next_range0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range0 =
      .ok (some 0#usize, range1) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) range0 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hs, he⟩
  subst opt
  have hs' : iter.start = range1.start := by
    apply UScalar.eq_of_val_eq
    simpa [range0, range1] using hs
  have he' : iter.end = range1.end := by simpa [range0, range1] using he
  have hi : iter = range1 := range_eq iter range1 hs' he'
  subst iter
  simpa only [range0] using hn

theorem next_range1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range1 =
      .ok (some 1#usize, range2) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) range1 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hs, he⟩
  subst opt
  have hs' : iter.start = range2.start := by
    apply UScalar.eq_of_val_eq
    simpa [range1, range2] using hs
  have he' : iter.end = range2.end := by simpa [range1, range2] using he
  have hi : iter = range2 := range_eq iter range2 hs' he'
  subst iter
  simpa only [range1] using hn

theorem next_range2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range2 =
      .ok (some 2#usize, range3) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) range2 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hs, he⟩
  subst opt
  have hs' : iter.start = range3.start := by
    apply UScalar.eq_of_val_eq
    simpa [range2, range3] using hs
  have he' : iter.end = range3.end := by simpa [range2, range3] using he
  have hi : iter = range3 := range_eq iter range3 hs' he'
  subst iter
  simpa only [range2] using hn

theorem next_range3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range3 =
      .ok (some 3#usize, range4) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) range3 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hs, he⟩
  subst opt
  have hs' : iter.start = range4.start := by
    apply UScalar.eq_of_val_eq
    simpa [range3, range4] using hs
  have he' : iter.end = range4.end := by simpa [range3, range4] using he
  have hi : iter = range4 := range_eq iter range4 hs' he'
  subst iter
  simpa only [range3] using hn

theorem next_range4 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range4 =
      .ok (none, range4) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) range4 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hi⟩
  subst opt
  subst iter
  exact hn

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
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
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext, rfl, h⟩

private theorem body_success_is_cont
    (f : Slice U8) (libra : Array field.WideExact (4#usize))
    (iter iterNext : R) (j : U) (parts : W)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (flow : ControlFlow (R × W) W)
    (hbody : projectionBody f libra (iter, parts) = .ok flow) :
    ∃ partsNext, flow = .cont (iterNext, partsNext) := by
  unfold projectionBody _root_.AspisR1S9PairCallerStepV1.weights.Weights.pair_s2_libra_parts_projection_loop.body at hbody
  rw [hnext] at hbody
  simp only [bind_tc_ok] at hbody
  obtain ⟨old, hold, hrest⟩ := bind_success _ _ _ hbody
  obtain ⟨value, hfield, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨coef, hcoef, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨prod, hprod, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨total, htotal, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨out, hupdate, hret⟩ := bind_success _ _ _ hrest
  exact ⟨out, (Result.ok.inj hret).symm⟩

/-- The concrete four-body range trace. Each body witness is the exact emitted
projection loop-body call at one of the checked Range.next indices. -/
structure ProjectionTrace4 (f : Slice U8) (libra : Array field.WideExact (4#usize))
    (initial output : W) : Type where
  p1 : W
  p2 : W
  p3 : W
  hbody0 : projectionBody f libra (range0, initial) = .ok (.cont (range1, p1))
  hbody1 : projectionBody f libra (range1, p1) = .ok (.cont (range2, p2))
  hbody2 : projectionBody f libra (range2, p2) = .ok (.cont (range3, p3))
  hbody3 : projectionBody f libra (range3, p3) = .ok (.cont (range4, output))

theorem loop_success_extracts_projection_trace4
    (f : Slice U8) (libra : Array field.WideExact (4#usize))
    (initial output : W)
    (hloop : projectionLoop f libra initial = .ok output) :
    Nonempty (ProjectionTrace4 f libra initial output) := by
  let step : R × W → Result (ControlFlow (R × W) W) := projectionBody f libra
  have hloop' : Aeneas.Std.loop step (range0, initial) = .ok output := by
    unfold projectionLoop _root_.AspisR1S9PairCallerStepV1.weights.Weights.pair_s2_libra_parts_projection_loop at hloop
    change Aeneas.Std.loop (projectionBody f libra) (range0, initial) = .ok output
    exact hloop
  rcases loop_success_cases step (range0, initial) output hloop' with hdone0 | hcont0
  · have hbodyDone : projectionBody f libra (range0, initial) = .ok (.done output) := by
      simpa [step] using hdone0
    obtain ⟨_, hshape⟩ := body_success_is_cont f libra range0 range1 0#usize initial
      next_range0 (.done output) hbodyDone
    cases hshape
  · obtain ⟨state1, hstep0, htail0⟩ := hcont0
    have hbody0 : projectionBody f libra (range0, initial) = .ok (.cont state1) := by
      simpa [step] using hstep0
    obtain ⟨p1, hshape0⟩ := body_success_is_cont f libra range0 range1 0#usize initial
      next_range0 (.cont state1) hbody0
    have hstate1 : state1 = (range1, p1) := by
      cases state1 with
      | mk iter1' parts1' =>
        injection hshape0 with hpair
    subst state1
    rcases loop_success_cases step (range1, p1) output htail0 with hdone1 | hcont1
    · have hbodyDone : projectionBody f libra (range1, p1) = .ok (.done output) := by
        simpa [step] using hdone1
      obtain ⟨_, hshape⟩ := body_success_is_cont f libra range1 range2 1#usize p1
        next_range1 (.done output) hbodyDone
      cases hshape
    · obtain ⟨state2, hstep1, htail1⟩ := hcont1
      have hbody1 : projectionBody f libra (range1, p1) = .ok (.cont state2) := by
        simpa [step] using hstep1
      obtain ⟨p2, hshape1⟩ := body_success_is_cont f libra range1 range2 1#usize p1
        next_range1 (.cont state2) hbody1
      have hstate2 : state2 = (range2, p2) := by
        cases state2 with
        | mk iter2' parts2' =>
          injection hshape1 with hpair
      subst state2
      rcases loop_success_cases step (range2, p2) output htail1 with hdone2 | hcont2
      · have hbodyDone : projectionBody f libra (range2, p2) = .ok (.done output) := by
          simpa [step] using hdone2
        obtain ⟨_, hshape⟩ := body_success_is_cont f libra range2 range3 2#usize p2
          next_range2 (.done output) hbodyDone
        cases hshape
      · obtain ⟨state3, hstep2, htail2⟩ := hcont2
        have hbody2 : projectionBody f libra (range2, p2) = .ok (.cont state3) := by
          simpa [step] using hstep2
        obtain ⟨p3, hshape2⟩ := body_success_is_cont f libra range2 range3 2#usize p2
          next_range2 (.cont state3) hbody2
        have hstate3 : state3 = (range3, p3) := by
          cases state3 with
          | mk iter3' parts3' =>
            injection hshape2 with hpair
        subst state3
        rcases loop_success_cases step (range3, p3) output htail2 with hdone3 | hcont3
        · have hbodyDone : projectionBody f libra (range3, p3) = .ok (.done output) := by
            simpa [step] using hdone3
          obtain ⟨_, hshape⟩ := body_success_is_cont f libra range3 range4 3#usize p3
            next_range3 (.done output) hbodyDone
          cases hshape
        · obtain ⟨state4, hstep3, htail3⟩ := hcont3
          have hbody3 : projectionBody f libra (range3, p3) = .ok (.cont state4) := by
            simpa [step] using hstep3
          obtain ⟨p4, hshape3⟩ := body_success_is_cont f libra range3 range4 3#usize p3
            next_range3 (.cont state4) hbody3
          have hstate4 : state4 = (range4, p4) := by
            cases state4 with
            | mk iter4' parts4' =>
              injection hshape3 with hpair
          subst state4
          have hterminal : projectionBody f libra (range4, p4) = .ok (.done p4) := by
            unfold projectionBody _root_.AspisR1S9PairCallerStepV1.weights.Weights.pair_s2_libra_parts_projection_loop.body
            rw [next_range4]
            rfl
          rcases loop_success_cases step (range4, p4) output htail3 with hdone4 | hcont4
          · have hdoneBody : projectionBody f libra (range4, p4) = .ok (.done output) := by
              simpa [step] using hdone4
            have heq := Result.ok.inj (hterminal.symm.trans hdoneBody)
            injection heq with hout
            subst output
            exact ⟨⟨p1, p2, p3, by simpa [step] using hbody0,
              by simpa [step] using hbody1, by simpa [step] using hbody2,
              by simpa [step] using hbody3⟩⟩
          · obtain ⟨stateNext, hnextBody, _⟩ := hcont4
            have hcontBody : projectionBody f libra (range4, p4) = .ok (.cont stateNext) := by
              simpa [step] using hnextBody
            have heq := Result.ok.inj (hterminal.symm.trans hcontBody)
            cases heq

#print axioms loop_success_extracts_projection_trace4
end AspisR1S9PairProjectionTrace4V1
