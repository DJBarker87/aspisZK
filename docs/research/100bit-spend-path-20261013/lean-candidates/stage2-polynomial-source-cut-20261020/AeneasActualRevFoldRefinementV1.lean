import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.RevFoldRefinement

/-- Exact Aeneas iterator type reached by the polynomial's `Range<usize>`.
    This module imports only the Aeneas standard-library owner, not generated
    protocol `Funs` or `FunsExternal` modules. -/
abbrev ActualRevRange :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

def actualRevNext (iter : ActualRevRange) :
    Result (Option Usize × ActualRevRange) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
    iter

def actualInitialRevRange : ActualRevRange :=
  ⟨{ start := 0#usize, «end» := 7#usize }⟩

/-- Kernel-computed item trace of eight actual Aeneas `Rev.next` calls. The
    eighth call records termination, so `some` proves seven successful items
    followed by `none`, with no error/divergence on the path. -/
def actualRevNextTrace : Nat → ActualRevRange → Option (List Nat)
  | 0, _ => some []
  | n + 1, iter =>
      match actualRevNext iter with
      | .ok (none, _) => some []
      | .ok (some index, iter1) => do
          let rest ← actualRevNextTrace n iter1
          some (index.val :: rest)
      | .fail _ => none
      | .div => none

theorem actual_rev_next_trace_zero_seven :
    actualRevNextTrace 8 actualInitialRevRange = some [6, 5, 4, 3, 2, 1, 0] := by
  decide

/-- Nat-indexed step fold corresponding to the seven indices in a half-open
    range `[0,n)` traversed from the back. -/
def reverseRangeFold {α : Type} (step : α → Nat → Result α) :
    Nat → α → Result α
  | 0, state => .ok state
  | n + 1, state => do
      let state1 ← step state n
      reverseRangeFold step n state1

/-- Result-aware transcription of the pinned default `rfold` source loop:
    repeatedly invoke Aeneas `Rev.next`; stop at `none`, otherwise call the
    monadic model of the source callback and continue. -/
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
      reverseRangeFold step 7 state := by
  simp [actualRfoldLoop, actualRevNext, actualInitialRevRange,
    reverseRangeFold]

#print core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
#print core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back
#print axioms actual_rev_next_trace_zero_seven
#print axioms actual_rfold_loop_zero_seven

end AspisR1CurrentWide.RevFoldRefinement
