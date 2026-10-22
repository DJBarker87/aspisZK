import AspisR1S9CandidateHelperV1.Funs
import Aeneas.Std.RangeIter
import S9CandidateBodyEvidenceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateTwoBodyCallsV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateBodyEvidenceV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)


def start0 : R := { start := 0#usize, «end» := 2#usize }
def start1 : R := { start := 1#usize, «end» := 2#usize }
def start2 : R := { start := 2#usize, «end» := 2#usize }

def body (ap0 ap1 : W) (extra : Array field.QM31 (2#usize)) :
    R × W → Result (ControlFlow (R × W) W) := fun s =>
  weights.factored_s2_libra_weights_loop.body ap0 ap1 extra s.1 s.2

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

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem active_body_success_is_cont (ap0 ap1 : W) (extra : Array field.QM31 (2#usize))
    (iter iterNext : R) (side : U) (weights : W) (flow : ControlFlow (R × W) W)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side, iterNext))
    (hbody : body ap0 ap1 extra (iter, weights) = .ok flow) :
    ∃ updated, flow = .cont (iterNext, updated) := by
  have hprefix := AspisR1S9CandidateBodyEvidenceV1.candidate_body_success_evidence
    ap0 ap1 extra iter iterNext side weights flow hnext hbody
  rcases hprefix with ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
    c0,c1,c2,c3,hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail⟩
  have hcur := htail
  unfold AspisR1S9CandidateBodyTermsV1.candidateAfterTerms at hcur
  repeat' (rcases bind_success_inv _ _ _ hcur with ⟨_, _, hcur⟩)
  split at hcur
  all_goals
    repeat' (rcases bind_success_inv _ _ _ hcur with ⟨_, _, hcur⟩)
    cases flow with
    | done final => cases Result.ok.inj hcur
    | cont nextState =>
        cases nextState with
        | mk iter' updated =>
            have hresult := Result.ok.inj hcur
            injection hresult with hpair
            have hiter : iter' = iterNext := congrArg Prod.fst hpair.symm
            exact ⟨updated, by rw [hiter]⟩

private theorem terminal_body_eq_done (ap0 ap1 : W) (extra : Array field.QM31 (2#usize))
    (iter : R) (weights : W)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter)) :
    body ap0 ap1 extra (iter, weights) = .ok (.done weights) := by
  unfold body _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
  rw [hnext]
  rfl

/-- Exact structural target to be proved: a successful extracted two-side
helper execution exposes its two successful active body calls and its terminal
body call, in source order. -/
theorem helper_success_two_body_calls (ap0 ap1 : W) (extra : Array field.QM31 (2#usize))
    (initial output : W)
    (hloop : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
      start0 ap0 ap1 extra initial = .ok output) :
    ∃ (iter1 iter2 : R) (middle : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize start0 =
        .ok (some 0#usize, iter1) ∧ iter1.start.val = 1 ∧ iter1.end = 2#usize ∧
      body ap0 ap1 extra (start0, initial) = .ok (.cont (iter1, middle)) ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter1 =
        .ok (some iter1.start, iter2) ∧ iter2.start.val = 2 ∧ iter2.end = 2#usize ∧
      body ap0 ap1 extra (iter1, middle) = .ok (.cont (iter2, output)) ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter2 =
        .ok (none, iter2) ∧
      body ap0 ap1 extra (iter2, output) = .ok (.done output) := by
  let step : R × W → Result (ControlFlow (R × W) W) := body ap0 ap1 extra
  have hloop' : Aeneas.Std.loop step (start0, initial) = .ok output := by
    change Aeneas.Std.loop
      (fun s => _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
        ap0 ap1 extra s.1 s.2) (start0, initial) = .ok output
    simpa [step, body, _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop] using hloop
  have hnextSpec0 := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) start0 (by decide)
  obtain ⟨pair0, hnext0, hpost0⟩ := WP.spec_imp_exists hnextSpec0
  rcases pair0 with ⟨opt0, iter1⟩
  rcases hpost0 with ⟨hopt0, hstart1, hend1⟩
  subst opt0
  have hnext0' : core.iter.range.IteratorRange.next core.iter.range.StepUsize start0 =
      .ok (some 0#usize, iter1) := by simpa [start0] using hnext0
  have hstart1' : iter1.start.val = 1 := by simpa [start0] using hstart1
  have hend1' : iter1.end = 2#usize := by simpa [start0] using hend1
  rcases loop_success_cases step (start0, initial) output hloop' with hdone0 | hcont0
  · obtain ⟨w, hbad⟩ := active_body_success_is_cont
      ap0 ap1 extra start0 iter1 0#usize initial (.done output) hnext0' hdone0
    cases hbad
  · obtain ⟨state1, hbody0, htail0⟩ := hcont0
    rcases state1 with ⟨iter1', middle⟩
    have hstate1 : iter1' = iter1 := by
      obtain ⟨updated, heq⟩ := active_body_success_is_cont
        ap0 ap1 extra start0 iter1 0#usize initial (.cont (iter1', middle)) hnext0' hbody0
      injection heq with hpair
      have hiter : iter1' = iter1 := (congrArg Prod.fst hpair)
      exact hiter
    subst iter1'
    have hstart1val : iter1.start.val = 1 := hstart1'
    have hend1val : iter1.end.val = 2 := by rw [hend1']; rfl
    have hnextSpec1 := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter1 (by omega)
    obtain ⟨pair1, hnext1, hpost1⟩ := WP.spec_imp_exists hnextSpec1
    rcases pair1 with ⟨opt1, iter2⟩
    rcases hpost1 with ⟨hopt1, hstart2, hend2⟩
    subst opt1
    have hnext1' : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter1 =
        .ok (some iter1.start, iter2) := by simpa using hnext1
    have hstart2' : iter2.start.val = 2 := by
      rw [hstart1'] at hstart2
      have hendval : (2#usize).val = 2 := by rfl
      simpa [hendval] using hstart2
    have hend2' : iter2.end = 2#usize := by rw [hend1'] at hend2; exact hend2
    rcases loop_success_cases step (iter1, middle) output htail0 with hdone1 | hcont1
    · obtain ⟨w, hbad⟩ := active_body_success_is_cont
        ap0 ap1 extra iter1 iter2 iter1.start middle (.done output) hnext1' hdone1
      cases hbad
    · obtain ⟨state2, hbody1, htail1⟩ := hcont1
      rcases state2 with ⟨iter2', final⟩
      have hstate2 : ∃ updated, iter2' = iter2 ∧ final = updated := by
        obtain ⟨updated, heq⟩ := active_body_success_is_cont
          ap0 ap1 extra iter1 iter2 iter1.start middle
          (.cont (iter2', final)) hnext1' hbody1
        injection heq with hpair
        have hiter : iter2' = iter2 := (congrArg Prod.fst hpair)
        have hfinal : final = updated := (congrArg Prod.snd hpair)
        exact ⟨updated, hiter, hfinal⟩
      rcases hstate2 with ⟨updated, hiter2, hfinalUpdated⟩
      subst iter2'
      have hnextSpec2 := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize) (by intros; rfl) iter2
        (by rw [hstart2', hend2']; rfl)
      obtain ⟨pair2, hnext2, hpost2⟩ := WP.spec_imp_exists hnextSpec2
      rcases pair2 with ⟨opt2, iter3⟩
      rcases hpost2 with ⟨hopt2, hiter3⟩
      subst opt2
      have hir : iter3 = iter2 := hiter3
      subst iter3
      have hnext2' : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter2 =
          .ok (none, iter2) := by simpa using hnext2
      have hdoneFinal := terminal_body_eq_done ap0 ap1 extra iter2 final hnext2'
      have hfinalOutput : final = output := by
        rcases loop_success_cases step (iter2, final) output htail1 with hdone | hcont
        · have heq := Result.ok.inj (hdoneFinal.symm.trans hdone)
          injection heq
        · obtain ⟨next, hcont, _⟩ := hcont
          have heq := Result.ok.inj (hdoneFinal.symm.trans hcont)
          cases heq
      have hupdatedOutput : updated = output := hfinalUpdated.symm.trans hfinalOutput
      subst final
      subst updated
      have hdone2 := terminal_body_eq_done ap0 ap1 extra iter2 output hnext2'
      exact ⟨iter1, iter2, middle, hnext0', hstart1', hend1', hbody0,
        hnext1', hstart2', hend2', hbody1, hnext2', hdone2⟩

#print axioms helper_success_two_body_calls
#print axioms active_body_success_is_cont

end AspisR1S9CandidateTwoBodyCallsV1
