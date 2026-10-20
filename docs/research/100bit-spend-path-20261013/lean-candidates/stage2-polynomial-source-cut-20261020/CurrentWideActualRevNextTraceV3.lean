import CurrentWideUnrolledRecordPolynomialV1

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

theorem actual_rev_next_trace_zero_seven :
    actualRevNextTrace 8 actualInitialRevRange = some [6, 5, 4, 3, 2, 1, 0] := by
  decide

#print axioms actual_rev_next_trace_zero_seven

end AspisR1CurrentWide.Proof
