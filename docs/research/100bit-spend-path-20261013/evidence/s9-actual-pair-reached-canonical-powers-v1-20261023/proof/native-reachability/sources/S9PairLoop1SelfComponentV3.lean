import S9LoopOutputPropertyV1
import S9RangeNextProgressV2
import AspisR1S9ProductionPairCutV1.Funs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1

namespace AspisR1S9PairLoop1SelfComponentV3

private abbrev Iter := core.ops.range.Range Std.Usize
private abbrev Common := Array aspis_core.field.QM31 16#usize
private abbrev State := Iter × Common
private abbrev Output := weights.Weights × Common

private def ContinuesAt (iter : Iter)
    (r : Result (ControlFlow State Output)) : Prop :=
  ∀ out, r = .ok out → ∃ common, out = .cont (iter, common)

private theorem bind_continuesAt {α : Type} (iter : Iter)
    (m : Result α) (k : α → Result (ControlFlow State Output))
    (hk : ∀ x, ContinuesAt iter (k x)) :
    ContinuesAt iter (do let x ← m; k x) := by
  intro out hout
  cases hm : m with
  | fail e => simp only [hm, bind_tc_fail] at hout; cases hout
  | div => simp only [hm, bind_tc_div] at hout; cases hout
  | ok x =>
      simp only [hm, bind_tc_ok] at hout
      exact hk x out hout

private theorem pair_loop1_some_tail_continuesAt
    (self : weights.Weights) (iter1 : Iter) (common : Common) (j : Std.Usize) :
    ContinuesAt iter1 (do
      let i ← lift (j &&& 3#usize)
      let a ← Array.index_usize self.factors 0#usize
      let a1 ← Array.index_usize a 2#usize
      let q ← Array.index_usize a1 i
      let i1 ← lift (Std.Usize.wrapping_shr j 2#u32)
      let a2 ← Array.index_usize a 3#usize
      let q1 ← Array.index_usize a2 i1
      let q2 ← aspis_core.field.QM31.mul q q1
      let a3 ← Array.update common j q2
      ok (cont (iter1, a3))) := by
  unfold ContinuesAt
  apply bind_continuesAt
  intro i
  apply bind_continuesAt
  intro a
  apply bind_continuesAt
  intro a1
  apply bind_continuesAt
  intro q
  apply bind_continuesAt
  intro i1
  apply bind_continuesAt
  intro a2
  apply bind_continuesAt
  intro q1
  apply bind_continuesAt
  intro q2
  apply bind_continuesAt
  intro a3
  intro out hout
  have hvalue : ControlFlow.cont (iter1, a3) = out := Result.ok.inj hout
  cases hvalue
  exact ⟨a3, rfl⟩

private theorem range_next_some_progress (iter iterNext : Iter) (j : Std.Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext)) :
    iter.start.val < iter.end.val ∧
      iterNext.start.val = iter.start.val + 1 ∧ iterNext.end = iter.end :=
  AspisR1S9RangeNextProgressV2.range_next_some_progress iter iterNext j hnext

private theorem pair_loop1_body_done_first
    (self : weights.Weights) (iter : Iter) (common : Common) (out : Output)
    (hbody : weights.Weights.pair_loop1.body self iter common =
      .ok (.done out)) : out.1 = self := by
  unfold weights.Weights.pair_loop1.body at hbody
  cases hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp only [hnext, bind_tc_fail] at hbody; cases hbody
  | div => simp only [hnext, bind_tc_div] at hbody; cases hbody
  | ok pair =>
      rcases pair with ⟨opt, iter1⟩
      cases opt with
      | none =>
          simp only [hnext, bind_tc_ok] at hbody
          have hp : (self, common) = out :=
            ControlFlow.done.inj (Result.ok.inj hbody)
          exact (congrArg Prod.fst hp).symm
      | some j =>
          simp only [hnext, bind_tc_ok] at hbody
          have hshape := pair_loop1_some_tail_continuesAt self iter1 common j
          obtain ⟨nextState, heq⟩ := hshape (.done out) hbody
          cases heq

private theorem pair_loop1_body_cont_decreases
    (self : weights.Weights) (iter : Iter) (common : Common)
    (iterNext : Iter) (commonNext : Common)
    (hbody : weights.Weights.pair_loop1.body self iter common =
      .ok (.cont (iterNext, commonNext))) :
    iterNext.end.val - iterNext.start.val < iter.end.val - iter.start.val := by
  unfold weights.Weights.pair_loop1.body at hbody
  cases hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp only [hnext, bind_tc_fail] at hbody; cases hbody
  | div => simp only [hnext, bind_tc_div] at hbody; cases hbody
  | ok pair =>
      rcases pair with ⟨opt, iter1⟩
      cases opt with
      | none =>
          simp only [hnext, bind_tc_ok] at hbody
          cases hbody
      | some j =>
          simp only [hnext, bind_tc_ok] at hbody
          have hshape := pair_loop1_some_tail_continuesAt self iter1 common j
          obtain ⟨common1, heq⟩ := hshape (.cont (iterNext, commonNext)) hbody
          have hiter : iterNext = iter1 := by
            have hc := ControlFlow.cont.inj heq
            exact congrArg Prod.fst hc
          subst iterNext
          have hp := range_next_some_progress iter iter1 j hnext
          have hendVal : iter1.end.val = iter.end.val := congrArg UScalar.val hp.2.2
          omega

/-- The first `Weights` component of a successful `pair_loop1` loop result is
unchanged.  The body stores no updated Weights value: its terminal constructor
returns the captured `self`, while each successful continuation advances the
range iterator and changes only the common array. -/
theorem pair_loop1_first_component
    (iter : Iter) (self selfOut : weights.Weights) (common commonOut : Common)
    (hloop : weights.Weights.pair_loop1 iter self common = .ok (selfOut, commonOut)) :
    selfOut = self := by
  let step : State → Result (ControlFlow State Output) :=
    fun s => weights.Weights.pair_loop1.body self s.1 s.2
  have hloop' : Aeneas.Std.loop step (iter, common) = .ok (selfOut, commonOut) := by
    change Aeneas.Std.loop
      (fun s => weights.Weights.pair_loop1.body self s.1 s.2) (iter, common) =
      .ok (selfOut, commonOut)
    simpa only [weights.Weights.pair_loop1] using hloop
  exact AspisR1S9LoopOutputPropertyV1.loop_output_property
    step (fun s => s.1.end.val - s.1.start.val)
    (fun out : Output => out.1 = self)
    (by
      intro s out hdone
      exact pair_loop1_body_done_first self s.1 s.2 out hdone)
    (by
      intro s s' hcont
      exact pair_loop1_body_cont_decreases self s.1 s.2 s'.1 s'.2 hcont)
    (iter, common) (selfOut, commonOut) hloop'

#print axioms pair_loop1_first_component

end AspisR1S9PairLoop1SelfComponentV3
