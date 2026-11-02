import PV_B3P_NthSource559227
namespace PV_B3P_NthFormatting559227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthKernelGuard559227 PV_B3P_NthSource559227
set_option autoImplicit false
/-- Checked increment's entire success value, for an arbitrary handler. -/
theorem increment_value (handler : Str → Result Never) (item end_ : Usize)
    (guard : item.val < end_.val) :
    increment_with handler item = .ok (Usize.wrapping_add item 1#usize) := by
  simp only [increment_with,increment_wrap item end_ guard,bind_tc_ok]

/-- The extracted control with its only panic continuation left arbitrary. This
is a source-control interpretation; no always-Ok formatter model is involved. -/
def source_with (handler : Str → Result Never) (r : Range Usize) (n : Usize) :
    Result (Option Usize × Range Usize) := do
  let candidate ← core.iter.range.StepUsize.forward_checked r.start n
  match candidate with
  | none => .ok (none,{r with start := r.end})
  | some item =>
      if item.val < r.end.val then do
        let next ← increment_with handler item
        .ok (some item,{r with start := next})
      else .ok (none,{r with start := r.end})

theorem arbitrary_handler_binding (handler : Str → Result Never)
    (r : Range Usize) (n : Usize) : source_with handler r n = source r n := by
  unfold source_with source
  apply congrArg (Aeneas.Std.bind _)
  funext candidate
  cases candidate with
  | none => rfl
  | some item =>
      by_cases guard : item.val < r.end.val
      · simp only [guard,if_true,increment_value handler item r.end guard,bind_tc_ok]
      · simp only [guard,if_false]

theorem nth_formatting_independent (first second : Str → Result Never)
    (r : Range Usize) (n : Usize) :
    source_with first r n = source_with second r n :=
  (arbitrary_handler_binding first r n).trans (arbitrary_handler_binding second r n).symm

#print axioms increment_value
#print axioms arbitrary_handler_binding
#print axioms nth_formatting_independent
end PV_B3P_NthFormatting559227
