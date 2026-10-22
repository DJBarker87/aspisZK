import ExtractedIteratorFoldV1
import AspisR1S9HelperP6.ExternalSlotsV1
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9TransparentFoldRangeLawV1

abbrev U := Std.Usize
abbrev Range := core.ops.range.Range U

/-- State transition used by the P6 range model; it exactly preserves the
emitted FnMut callback result and returned closure state. -/
def foldStep {B F : Type}
    (callback : core.ops.function.FnMut F (B × U) B) :
    (B × F) → U → Result (B × F) := fun state index => do
  let (value, closure') ← callback.call_mut state.2 (state.1, index)
  ok (value, closure')

private theorem rangeNext_some_exact (range : Range)
    (hlt : range.start.val < range.end.val) :
    ∃ next,
      AspisR1S3S9RangeFoldP6.rangeNext range =
        .ok (some range.start, next) ∧
      next.start.val = range.start.val + 1 ∧ next.end = range.end := by
  have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) range hlt
  obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
  rcases pair with ⟨opt, next⟩
  rcases hpost with ⟨hopt, hstart, hend⟩
  subst opt
  exact ⟨next, hnext, hstart, hend⟩

private theorem rangeNext_none_exact (range : Range)
    (hge : range.start.val ≥ range.end.val) :
    AspisR1S3S9RangeFoldP6.rangeNext range = .ok (none, range) := by
  have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) range hge
  obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
  rcases pair with ⟨opt, next⟩
  rcases hpost with ⟨hopt, hiter⟩
  subst opt
  have hnextEq : next = range := hiter
  rw [hnextEq] at hnext
  simpa [AspisR1S3S9RangeFoldP6.rangeNext] using hnext

/-- One emitted loop iteration when `next` returns an item. -/
theorem extracted_fold_some {Self B F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (callback : core.ops.function.FnMut F (B × Item) B)
    (self next : Self) (initial : B) (closure : F) (item : Item)
    (hnext : iteratorInst.next self = .ok (some item, next)) :
    AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
        iteratorInst callback self initial closure =
      (do
        let (initial', closure') ← callback.call_mut closure (initial, item)
        AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
          iteratorInst callback next initial' closure') := by
  unfold AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
    AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default_loop.body,
    hnext, bind_tc_ok]
  cases hcall : callback.call_mut closure (initial, item) with
  | fail e => simp [hcall]
  | div => simp [hcall]
  | ok pair => rcases pair with ⟨initial', closure'⟩; simp [hcall]

/-- One emitted loop iteration when `next` reaches the end. -/
theorem extracted_fold_none {Self B F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (callback : core.ops.function.FnMut F (B × Item) B)
    (self next : Self) (initial : B) (closure : F)
    (hnext : iteratorInst.next self = .ok (none, next)) :
    AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
        iteratorInst callback self initial closure = .ok initial := by
  unfold AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
    AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default_loop.body,
    hnext, bind_tc_ok]
  rfl

/-- The exact extracted `Iterator::fold.default` loop agrees with the
operational range fold for every `Range<usize>`. The measure is the remaining
range length; the final `next = None` is handled by the emitted loop body, and
callback failure/divergence is preserved on both sides. -/
theorem extracted_fold_eq_rangeFoldRun {B F : Type}
    (callback : core.ops.function.FnMut F (B × U) B)
    (range : Range) (initial : B) (closure : F) :
    AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callback range initial closure =
      (do
        let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun
          (range.end.val - range.start.val) range (foldStep callback) (initial, closure)
        ok value) := by
  let P := fun (n : Nat) => ∀ (range : Range) (initial : B) (closure : F),
    range.end.val - range.start.val = n →
    AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callback range initial closure =
      (do
        let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun
          n range (foldStep callback) (initial, closure)
        ok value)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro range initial closure hlen
      by_cases hlt : range.start.val < range.end.val
      · cases n with
        | zero => omega
        | succ fuel =>
          obtain ⟨next, hnext, hstart, hend⟩ := rangeNext_some_exact range hlt
          have hnextLen : next.end.val - next.start.val = fuel := by
            have hendVal : next.end.val = range.end.val := by simpa using congrArg (fun x : Std.Usize => x.val) hend
            omega
          have hnextIter :
              (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize).next range =
                .ok (some range.start, next) := by
            simpa [AspisR1S3S9RangeFoldP6.rangeNext] using hnext
          rw [extracted_fold_some _ callback range next initial closure range.start hnextIter]
          cases hcall : callback.call_mut closure (initial, range.start) with
          | fail e =>
              simp [AspisR1S3S9RangeFoldP6.rangeFoldRun, hnext, foldStep, hcall]
          | div =>
              simp [AspisR1S3S9RangeFoldP6.rangeFoldRun, hnext, foldStep, hcall]
          | ok pair =>
              rcases pair with ⟨value, closure'⟩
              have hrec := ih fuel (by omega) next value closure' hnextLen
              simp [AspisR1S3S9RangeFoldP6.rangeFoldRun, hnext, foldStep, hcall,
                hrec]
      · have hge : range.start.val ≥ range.end.val := by omega
        have hzero : n = 0 := by omega
        subst n
        have hnext := rangeNext_none_exact range hge
        have hnextIter :
            (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize).next range =
              .ok (none, range) := by
          simpa [AspisR1S3S9RangeFoldP6.rangeNext] using hnext
        rw [extracted_fold_none _ callback range range initial closure hnextIter]
        simp [AspisR1S3S9RangeFoldP6.rangeFoldRun, hzero]
  exact hP (range.end.val - range.start.val) range initial closure rfl

/-- Install the exact transparent generated fold into the typed P6 slot. -/
@[reducible] def extractedFoldOperation {Self B F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (callback : core.ops.function.FnMut F (B × Item) B)
    (self : Self) (initial : B) (closure : F) : Result B :=
  AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
    iteratorInst callback self initial closure

@[reducible] def installExtractedFold
    (ops : AspisR1S9HelperP6.FieldOps) : AspisR1S9HelperP6.FieldOps :=
  { ops with iterFold := @extractedFoldOperation }

theorem installed_extracted_fold_satisfies_P6
    (ops : AspisR1S9HelperP6.FieldOps) :
    AspisR1S9HelperP6.IteratorFoldRangeP6Law (installExtractedFold ops) := by
  intro B F callback range initial closure
  change extractedFoldOperation
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      callback range initial closure =
    (do
      let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun
        (range.end.val - range.start.val) range (foldStep callback) (initial, closure)
      ok value)
  exact extracted_fold_eq_rangeFoldRun callback range initial closure

#print axioms extracted_fold_eq_rangeFoldRun
#print axioms installed_extracted_fold_satisfies_P6

end AspisR1S9TransparentFoldRangeLawV1
