import NMS_R2N_RSLScalarEq
set_option autoImplicit false
noncomputable section
namespace NMS_R2KeyEq
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
/-- Reuse the coherent symbolic std slice law at the exact two array slices;
no concrete key bytes or fixed-length loop is normalized. -/
theorem native (x y : Aeneas.Std.Array U8 32#usize) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 x y = ok (decide (x ≠ y)) := by
 have same : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 x y =
   ok (decide (x.val = y.val)) := AspisS6StdByteSlice.eq_exact x.to_slice y.to_slice
 unfold core.array.equality.PartialEqArray.ne
 rw [same,bind_tc_ok]
 congr 1
 by_cases h : x = y
 · subst y
   simp
 · have values : x.val ≠ y.val := fun equal => h (Subtype.ext equal)
   simp [h,values]
#print axioms native
end NMS_R2KeyEq
