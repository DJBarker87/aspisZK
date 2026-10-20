import CurrentWideUnrolledRecordPolynomialV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

/-- The actual Aeneas `Rev<Range<usize>>::next` type used by the generated
    iterator adapter. The range state is retained after each next call. -/
abbrev ActualRevRange :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

/-- One invocation of the generated Aeneas `Rev.next` implementation for a
    `Range<usize>` whose `DoubleEndedIterator` implementation is `StepUsize`. -/
def actualRevNext (iter : ActualRevRange) :
    Result (Option Usize × ActualRevRange) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
    iter

/-- Result-aware operational reading of the `while let Some(i) = next()` loop
    in the pinned default `DoubleEndedIterator::rfold`. `fuel` bounds the
    number of next calls; a `none` result terminates early. -/
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

def actualInitialRevRange : ActualRevRange :=
  ⟨{ start := 0#usize, «end» := 7#usize }⟩

/-- This is a reduction of the actual Aeneas `Rev.next` / `Range.next_back`
    definitions for the fixed seven-element range, not a model indexed by Nat.
    Eight fuel steps include the terminating `none` observation. -/
theorem actual_rev_next_trace_zero_seven :
    actualRevNextTrace 8 actualInitialRevRange = some [6, 5, 4, 3, 2, 1, 0] := by
  native_decide

#print axioms actual_rev_next_trace_zero_seven

end AspisR1CurrentWide.Proof
