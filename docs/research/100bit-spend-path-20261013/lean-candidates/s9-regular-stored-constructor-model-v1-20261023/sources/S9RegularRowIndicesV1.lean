import S9ActualProcessKindTensorReachedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RegularRowIndicesV1
open AspisR1S9ActualProcessKindTensorReachedV1

/-- Existing actual wrapping subtraction is ordinary subtraction in this
source-proved non-underflow case; size remains opaque/symbolic. -/
theorem wrapping_sub_val_of_le (x y : Usize) (hy : y.val≤x.val) :
    (Usize.wrapping_sub x y).val=x.val-y.val := by
  have hx := x.hSize
  have hys := y.hSize
  have hf : x.val+(UScalar.size .Usize-y.val)=(x.val-y.val)+UScalar.size .Usize := by omega
  have hs : x.val-y.val<UScalar.size .Usize := by omega
  rw [Usize.wrapping_sub_val_eq,hf]
  simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hs]

/-- Literal source regular kinds1/2/3/5/6 map to constructor rows0/1/2/3/4. -/
theorem row_one : (rowOfKind 1#usize).val=0 := by
  change (Usize.wrapping_sub 1#usize 1#usize).val=0
  rw [wrapping_sub_val_of_le _ _ (by decide)]
  rfl
theorem row_two : (rowOfKind 2#usize).val=1 := by
  change (Usize.wrapping_sub 2#usize 1#usize).val=1
  rw [wrapping_sub_val_of_le _ _ (by decide)]
  rfl
theorem row_three : (rowOfKind 3#usize).val=2 := by
  change (Usize.wrapping_sub 3#usize 1#usize).val=2
  rw [wrapping_sub_val_of_le _ _ (by decide)]
  rfl
theorem row_five : (rowOfKind 5#usize).val=3 := by
  change (Usize.wrapping_sub 5#usize 2#usize).val=3
  rw [wrapping_sub_val_of_le _ _ (by decide)]
  rfl
theorem row_six : (rowOfKind 6#usize).val=4 := by
  change (Usize.wrapping_sub 6#usize 2#usize).val=4
  rw [wrapping_sub_val_of_le _ _ (by decide)]
  rfl
#print axioms wrapping_sub_val_of_le
#print axioms row_one
#print axioms row_two
#print axioms row_three
#print axioms row_five
#print axioms row_six
end AspisR1S9RegularRowIndicesV1
