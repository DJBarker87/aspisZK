import NGG_Ref.Funs
import NFV_RequestGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_Compare
abbrev Key := Array U8 32#usize
theorem ne (a b : Key) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b =
      ok (decide (a.val ≠ b.val)) := by
  simp only [core.array.equality.PartialEqArray.ne,NFV_RequestGuards.array,bind_tc_ok]
  by_cases h : a.val = b.val <;> simp [h]
#print axioms ne
end NGG_Compare
