import CurrentWideReverseRangeFoldModelV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

abbrev ActualRevRange :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

def actualRevNext (iter : ActualRevRange) :
    Result (Option Usize × ActualRevRange) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
    iter

def actualInitialRevRange : ActualRevRange :=
  ⟨{ start := 0#usize, «end» := 7#usize }⟩

/-- Executable/result-aware transcription of the pinned default `rfold`
    `while let Some(i) = self.next_back()` loop. `fuel` is only a proof-side
    bound; the source loop terminates when `next` returns `none`. -/
def actualRfoldLoop {α : Type} : Nat → ActualRevRange →
    (α → Nat → Result α) → α → Result α
  | 0, _, _, state => .ok state
  | n + 1, iter, step, state => do
      let (item, iter1) ← actualRevNext iter
      match item with
      | none => .ok state
      | some index => do
          let state1 ← step state index.val
          actualRfoldLoop n iter1 step state1

theorem actual_rfold_loop_zero_seven {α : Type}
    (step : α → Nat → Result α) (state : α) :
    actualRfoldLoop 8 actualInitialRevRange step state =
      reverseRangeResult step 7 state := by
  simp [actualRfoldLoop, actualRevNext, actualInitialRevRange,
    reverseRangeResult]

#print axioms actual_rfold_loop_zero_seven

end AspisR1CurrentWide.Proof
