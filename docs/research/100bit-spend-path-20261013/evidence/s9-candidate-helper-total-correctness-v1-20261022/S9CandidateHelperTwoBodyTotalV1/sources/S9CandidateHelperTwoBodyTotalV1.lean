import S9CandidateActiveBodyTotalityV1
import S9CandidateTwoBodyCallsV1
import S9CandidateBodyPrefixV1
import S9FixedIteratorTransitionsV1
import S9HighTermSourceCellRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateHelperTwoBodyTotalV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateTwoBodyCallsV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev CA := Array CW (4#usize)
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PA := Array PW (4#usize)
abbrev Canonical := AspisR1S9P6AfterTermsTotalV1.Canonical
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem candidate_next_start0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start0 =
      .ok (some 0#usize, start1) := by
  simpa [AspisR1S9CandidateTwoBodyCallsV1.start0,
    AspisR1S9CandidateTwoBodyCallsV1.start1,
    AspisR1S9FactoredLoopTwoStepV4.start0,
    AspisR1S9FactoredLoopTwoStepV4.start1] using
      AspisR1S9FixedIteratorTransitionsV1.next_start0

private theorem candidate_next_start1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start1 =
      .ok (some 1#usize, start2) := by
  simpa [AspisR1S9CandidateTwoBodyCallsV1.start1,
    AspisR1S9CandidateTwoBodyCallsV1.start2,
    AspisR1S9FactoredLoopTwoStepV4.start1,
    AspisR1S9FactoredLoopTwoStepV4.start2] using
      AspisR1S9FixedIteratorTransitionsV1.next_start1

private theorem candidate_next_start2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start2 =
      .ok (none, start2) := by
  simpa [AspisR1S9CandidateTwoBodyCallsV1.start2,
    AspisR1S9FactoredLoopTwoStepV4.start2] using
      AspisR1S9FixedIteratorTransitionsV1.next_start2

/-- The actual two-iteration candidate loop succeeds from canonical reads of
its inputs. Each active body call is constructed from the same candidate
arithmetic and callback totality; the second body's old-cell premise is
transported from the first body's returned array. -/
theorem candidate_helper_total
    (ap0 ap1 : CA) (extra : Array CQ (2#usize)) (initial : CA)
    (hap0 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap0) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)) :
    ∃ output,
      _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
        AspisR1S9CandidateTwoBodyCallsV1.start0 ap0 ap1 extra initial = .ok output := by
  obtain ⟨middle,p6middle,hactive0,hmap0,hcanMiddle1⟩ :=
    AspisR1S9CandidateActiveBodyTotalityV1.candidate_active_body_total
      ap0 ap1 extra 0#usize start1 initial (by decide) hap0 hap1 hextra
      (by
        intro hne x hx
        exact False.elim (hne rfl))
  have hbody0 : AspisR1S9CandidateTwoBodyCallsV1.body
      ap0 ap1 extra (start0,initial) = .ok (.cont (start1,middle)) := by
    change _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra start0 initial = .ok (.cont (start1,middle))
    rw [AspisR1S9CandidateBodyPrefixV1.body_some_eq_candidateActiveBody
      ap0 ap1 extra start0 start1 0#usize initial candidate_next_start0]
    exact hactive0
  have hmiddleRead : ∀ (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W middle)
        1#usize = .ok x → Canonical x := by
    intro x hx
    change mapArray AspisR1S9CandidateHelperV1.toP6W middle = p6middle at hmap0
    rw [hmap0] at hx
    have hcell := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
      p6middle 1#usize x (by decide) hx
    rw [← hcell]
    exact hcanMiddle1
  obtain ⟨output,p6output,hactive1,hmap1,hcanOutput1⟩ :=
    AspisR1S9CandidateActiveBodyTotalityV1.candidate_active_body_total
      ap0 ap1 extra 1#usize start2 middle (by decide) hap0 hap1 hextra
      (by intro _ x hx; exact hmiddleRead x hx)
  have hbody1 : AspisR1S9CandidateTwoBodyCallsV1.body
      ap0 ap1 extra (start1,middle) = .ok (.cont (start2,output)) := by
    change _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra start1 middle = .ok (.cont (start2,output))
    rw [AspisR1S9CandidateBodyPrefixV1.body_some_eq_candidateActiveBody
      ap0 ap1 extra start1 start2 1#usize middle candidate_next_start1]
    exact hactive1
  have hbody2 : AspisR1S9CandidateTwoBodyCallsV1.body
      ap0 ap1 extra (start2,output) = .ok (.done output) := by
    unfold AspisR1S9CandidateTwoBodyCallsV1.body
      _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
    rw [candidate_next_start2]
    rfl
  let step : R × CA → Result (ControlFlow (R × CA) CA) :=
    AspisR1S9CandidateTwoBodyCallsV1.body ap0 ap1 extra
  have hloop : Aeneas.Std.loop step (start0,initial) = .ok output := by
    dsimp only [step]
    rw [Aeneas.Std.loop.eq_def,hbody0]
    dsimp only
    rw [Aeneas.Std.loop.eq_def,hbody1]
    dsimp only
    rw [Aeneas.Std.loop.eq_def,hbody2]
  refine ⟨output, ?_⟩
  change Aeneas.Std.loop
    (fun s => _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra s.1 s.2) (start0,initial) = .ok output at hloop
  unfold _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
  exact hloop

#print axioms candidate_helper_total

end AspisR1S9CandidateHelperTwoBodyTotalV1
