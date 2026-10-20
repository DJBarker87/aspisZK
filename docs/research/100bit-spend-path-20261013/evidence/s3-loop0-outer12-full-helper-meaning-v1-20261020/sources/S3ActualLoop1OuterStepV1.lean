import S3ActualLoop1PrefixV5
import Aeneas.Std.RangeIter
import Aeneas.Std.SliceIter
import Aeneas.Std.Core.Iter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterStep

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

private theorem bind_success_inv {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def loop1InitialIter (low : Array field.WideExact 16#usize) :
    core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact) :=
  ⟨⟨Array.to_slice low, 0⟩, 0#usize⟩


abbrev OuterState := core.ops.range.Range Std.Usize × field.WideExact
abbrev OuterStepResult := Result (ControlFlow OuterState field.WideExact)

def outerDone (pair : field.WideExact) : ControlFlow OuterState field.WideExact :=
  done pair

def outerCont (iter : core.ops.range.Range Std.Usize) (pair : field.WideExact) :
    ControlFlow OuterState field.WideExact :=
  cont (iter, pair)

theorem loop1_iterator_setup (low : Array field.WideExact 16#usize) :
    (do
      let s ← lift (Array.to_slice low)
      let i ← core.slice.Slice.iter s
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter field.WideExact) i) =
      .ok (loop1InitialIter low) := by
  have hs : lift (Array.to_slice low) = .ok (Array.to_slice low) := rfl
  have hi : core.slice.Slice.iter (Array.to_slice low) =
      .ok ⟨Array.to_slice low, 0⟩ := rfl
  have he : core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter field.WideExact)
      ⟨Array.to_slice low, 0⟩ =
      .ok ⟨⟨Array.to_slice low, 0⟩, 0#usize⟩ := rfl
  rw [hs]
  simp only [bind_tc_ok]
  rw [hi]
  simp only [bind_tc_ok]
  rw [he]
  rfl

def loop1ActiveCall
    (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize)
    (ops : AspisR1GroupedPairActualFieldOpsV3.Operations)
    (group : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (pair : field.WideExact) : OuterStepResult := do
  let s ← lift (Array.to_slice low)
  let i ← core.slice.Slice.iter s
  let iter2 ← core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorSliceIter field.WideExact) i
  let weight ← weights.s2_grouped_inactive_pair_loop1_loop0 ops iter2 group
    field.WideExact.ZERO
  let coefficient ← Array.index_usize coefficients group
  let product ← ops.mul coefficient weight
  let pairNext ← ops.add pair product
  .ok (outerCont iterNext pairNext)

def loop1AfterRange
    (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize)
    (ops : AspisR1GroupedPairActualFieldOpsV3.Operations)
    (pair : field.WideExact)
    (item : Option Std.Usize × core.ops.range.Range Std.Usize) : OuterStepResult :=
  match item.1 with
  | none => .ok (outerDone pair)
  | some group => loop1ActiveCall low coefficients ops group item.2 pair

theorem outer_body_eq_after_range
    (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize)
    (ops : AspisR1GroupedPairActualFieldOpsV3.Operations)
    (iter : core.ops.range.Range Std.Usize)
    (pair : field.WideExact) :
    weights.s2_grouped_inactive_pair_loop1.body ops low coefficients iter pair =
      (do
        let item ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        loop1AfterRange low coefficients ops pair item) := by
  rfl

theorem outer_body_success_has_inner_run
    (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize)
    (iter : core.ops.range.Range Std.Usize)
    (pair : field.WideExact)
    (iterNext : core.ops.range.Range Std.Usize)
    (pairNext : field.WideExact)
    (hbody : weights.s2_grouped_inactive_pair_loop1.body actualOperations
        low coefficients iter pair = .ok (outerCont iterNext pairNext)) :
    ∃ group weight,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some group, iterNext) ∧
      weights.s2_grouped_inactive_pair_loop1_loop0 actualOperations
        (loop1InitialIter low) group field.WideExact.ZERO = .ok weight := by
  rw [outer_body_eq_after_range] at hbody
  obtain ⟨item, hnext, hrest⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter)
    (loop1AfterRange low coefficients actualOperations pair) (outerCont iterNext pairNext) hbody
  rcases item with ⟨option, iterResult⟩
  cases option with
  | none =>
      simp only [loop1AfterRange, outerDone] at hrest
      cases hrest
  | some group =>
      have hactive : loop1ActiveCall low coefficients actualOperations group
          iterResult pair = .ok (outerCont iterNext pairNext) := by
        simpa [loop1AfterRange] using hrest
      unfold loop1ActiveCall at hactive
      rw [show lift (Array.to_slice low) = .ok (Array.to_slice low) from rfl] at hactive
      simp only [bind_tc_ok] at hactive
      rw [show core.slice.Slice.iter (Array.to_slice low) =
          .ok ⟨Array.to_slice low, 0⟩ from rfl] at hactive
      simp only [bind_tc_ok] at hactive
      rw [show core.iter.traits.iterator.Iterator.enumerate.trait_default
          (core.iter.traits.iterator.IteratorSliceIter field.WideExact)
          ⟨Array.to_slice low, 0⟩ =
          .ok (loop1InitialIter low) from rfl] at hactive
      simp only [bind_tc_ok] at hactive
      obtain ⟨weight, hweight, hrest⟩ := bind_success_inv
        (weights.s2_grouped_inactive_pair_loop1_loop0 actualOperations
          (loop1InitialIter low) group field.WideExact.ZERO)
        (fun weight => do
          let coefficient ← Array.index_usize coefficients group
          let product ← actualOperations.mul coefficient weight
          let result ← actualOperations.add pair product
          .ok (outerCont iterResult result))
        (outerCont iterNext pairNext) hactive
      obtain ⟨coefficient, hcoefficient, hrest⟩ := bind_success_inv
        (Array.index_usize coefficients group)
        (fun coefficient => do
          let product ← actualOperations.mul coefficient weight
          let result ← actualOperations.add pair product
          .ok (outerCont iterResult result))
        (outerCont iterNext pairNext) hrest
      obtain ⟨product, hmul, hrest⟩ := bind_success_inv
        (actualOperations.mul coefficient weight)
        (fun product => do
          let result ← actualOperations.add pair product
          .ok (outerCont iterResult result))
        (outerCont iterNext pairNext) hrest
      obtain ⟨result, hadd, hfinal⟩ := bind_success_inv
        (actualOperations.add pair product)
        (fun result => .ok (outerCont iterResult result))
        (outerCont iterNext pairNext) hrest
      have hpair : iterResult = iterNext ∧ result = pairNext := by
        have hcf := Result.ok.inj hfinal
        cases hcf
        exact ⟨rfl, rfl⟩
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨group, weight, hnext, hweight⟩

#print axioms loop1_iterator_setup
#print axioms outer_body_success_has_inner_run

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterStep
