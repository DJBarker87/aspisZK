import PV_B3P_Std559Funs227
import PV_B3P_DependencyClosure557227
namespace PV_B3P_NthGuard559227
open Aeneas Aeneas.Std core.ops.range
set_option autoImplicit false
/-- The only expect_failed branch in extracted spec_nth follows the checked
increment by one of a value already strictly below the range end. -/
theorem increment_some (item end_ : Usize) (guard : item.val < end_.val) :
    ∃ next, core.iter.range.StepUsize.forward_checked item 1#usize = .ok (some next) ∧
      next.val = item.val + 1 := by
  have safe : item.val + (1#usize).val ≤ UScalar.max .Usize := by scalar_tac
  simp only [core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, safe, dif_pos]
  exact ⟨_,rfl,rfl⟩

/-- Source-level shape of the unreachable increment-failure branch. Its handler
has the complete Result carrier, including failure/divergence, not Unit/Ok. -/
def increment_with (panic_handler : Str → Result Never) (item : Usize) : Result Usize := do
  let next ← core.iter.range.StepUsize.forward_checked item 1#usize
  match next with
  | some value => .ok value
  | none => do
      let _ ← panic_handler (toStr "`Step` invariants not upheld")
      .fail .panic

theorem increment_format_independent (first second : Str → Result Never)
    (item end_ : Usize) (guard : item.val < end_.val) :
    increment_with first item = increment_with second item := by
  obtain ⟨next,run,_⟩ := increment_some item end_ guard
  simp only [increment_with,run,bind_tc_ok]

#print axioms increment_some
#print axioms increment_format_independent
end PV_B3P_NthGuard559227
