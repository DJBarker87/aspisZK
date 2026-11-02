import PV_B3P_NextFormatting569227
import PV_B3P_DirectInclusive17227
namespace PV_B3P_InclusiveFormatting569227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthFormattingFinal559227
set_option autoImplicit false
/-- Default inclusive next; exhaustion and singleton return do not increment. -/
def source (handler : Str → Result Never) (r : RangeInclusive Usize) :
    Result (Option Usize × RangeInclusive Usize) :=
  if r.exhausted = true ∨ r.end.val < r.start.val then .ok (none,r)
  else if r.start.val < r.end.val then do
    let next ← PV_B3P_NthFinalGuard559227.increment_with handler r.start
    .ok (some r.start,⟨next,r.end,false⟩)
  else .ok (some r.start,{r with exhausted := true})

theorem model_binding (handler : Str → Result Never) (r : RangeInclusive Usize) :
    source handler r =
      RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize r := by
  cases r with
  | mk first last exhausted =>
    rw [PV_B3P_Direct17227.inclusive_next_extraction17]
    unfold source
    by_cases empty : exhausted = true ∨ last.val < first.val
    · simp only [empty,if_true]
    · simp only [empty,if_false]
      by_cases guard : first.val < last.val
      · simp only [guard,if_true,increment_value handler first last guard,bind_tc_ok]
      · simp only [guard,if_false]

theorem handler_independent (first second : Str → Result Never) (r : RangeInclusive Usize) :
    source first r = source second r :=
  (model_binding first r).trans (model_binding second r).symm
#print axioms model_binding
#print axioms handler_independent
end PV_B3P_InclusiveFormatting569227
