import PV_B3P_RangeBinding13227
namespace PV_B3P_Loans14227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- Deployed Range<usize>::spec_next_back: test before unchecked subtraction,
then return the new end. No allocation or destructor is present. -/
def range_next_back14 (start finish : Usize) : Result (Option Usize × Usize) :=
  if start < finish then
    let last := Usize.wrapping_sub finish 1#usize
    .ok (some last,last)
  else .ok (none,finish)

theorem range_decrement_safe14 (start finish : Usize) (nonempty : start < finish) :
    1 ≤ finish.val := by scalar_tac

theorem range_next_back_value14 (start finish : Usize) (nonempty : start < finish) :
    (Usize.wrapping_sub finish 1#usize).val = finish.val-1 :=
  PV_B3P_Offset226V3.sub_value finish 1#usize (by scalar_tac)

theorem range_next_back_empty14 (start finish : Usize) (empty : ¬ start < finish) :
    range_next_back14 start finish = .ok (none,finish) := by
  simp only [range_next_back14,empty,if_false]

theorem range_next_back_step14 (start finish : Usize) (nonempty : start < finish) :
    range_next_back14 start finish =
      .ok (some (Usize.wrapping_sub finish 1#usize),Usize.wrapping_sub finish 1#usize) := by
  simp only [range_next_back14,nonempty,if_true]
#print axioms range_decrement_safe14
#print axioms range_next_back_value14
#print axioms range_next_back_empty14
#print axioms range_next_back_step14
end PV_B3P_Loans14227
