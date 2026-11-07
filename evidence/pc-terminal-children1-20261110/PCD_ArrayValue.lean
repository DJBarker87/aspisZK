import PCD_ArrayEq
set_option autoImplicit false
namespace PCD_ArrayValue
open Aeneas Aeneas.Std
/-- Complete no-error meaning of the extracted fixed-array equality. -/
theorem array_equal (a b : Array U32 8#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU32 a b =
      Result.ok (decide (a.val = b.val)) := by
  unfold core.array.equality.PartialEqArray.eq
  have lengths : a.length = b.length := by
    change a.val.length = b.val.length
    exact a.property.trans b.property.symm
  rw [if_pos lengths]
  have callback :
      (fun x : U32 × U32 => do
        let v ← core.cmp.PartialEqU32.ne x.1 x.2
        Result.ok (decide (¬v = true))) =
      (fun x : U32 × U32 => Result.ok (decide (x.1 = x.2))) := by
    funext pair
    rcases pair with ⟨x,y⟩
    by_cases eq : x = y <;>
      simp [core.cmp.PartialEqU32, liftFun2, lift,
        core.cmp.impls.PartialEqU32.ne, bind_tc_ok, eq]
  rw [callback]
  exact PCD_ArrayEq.zipped_equal a.val b.val (a.property.trans b.property.symm)
#print axioms array_equal
end PCD_ArrayValue
