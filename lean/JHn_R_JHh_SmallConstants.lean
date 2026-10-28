import Port3_Wrapping
set_option autoImplicit false
namespace AspisR1.JHh_SmallConstants
open Aeneas Aeneas.Std
/-- Tiny wrapping arithmetic only; avoids importing the checkpoint-output
cone merely to instantiate the generic count/slot bounds at batch zero. -/
theorem count0 : Usize.wrapping_sub 10#usize 0#usize=10#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_sub_val_eq]
  change (10+(UScalar.size .Usize-0))%UScalar.size .Usize=10
  have cap : 10<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
  rw [Nat.sub_zero,Nat.add_mod_right,Nat.mod_eq_of_lt cap]
#print axioms count0
theorem slot_add (k : Usize) (small : k.val≤4096) :
    Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) k=k := by
  have mul : Usize.wrapping_mul 3#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 0#usize (by decide))
  rw [mul]
  apply UScalar.eq_of_val_eq
  have zero : (0#usize : Usize).val=0 := by scalar_tac
  have bound : (0#usize : Usize).val+k.val≤4096 := by
    rw [zero,Nat.zero_add]
    exact small
  have law := Port3_Wrapping.wrap_add_value 0#usize k bound
  rw [zero,Nat.zero_add] at law
  exact law
#print axioms slot_add
theorem slot0 : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 0#usize=0#usize := slot_add _ (by decide)
#print axioms slot0
theorem slot1 : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 1#usize=1#usize := slot_add _ (by decide)
#print axioms slot1
theorem slot2 : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 2#usize=2#usize := slot_add _ (by decide)
#print axioms slot2
end AspisR1.JHh_SmallConstants
