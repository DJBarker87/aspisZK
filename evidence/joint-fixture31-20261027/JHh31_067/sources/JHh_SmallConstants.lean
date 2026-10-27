import Port3_Wrapping
set_option autoImplicit false
namespace AspisR1.JHh_SmallConstants
open Aeneas Aeneas.Std
/-- Tiny wrapping arithmetic only; avoids importing the checkpoint-output
cone merely to instantiate the generic count/slot bounds at batch zero. -/
theorem count0 : Usize.wrapping_sub 10#usize 0#usize=10#usize := by rfl
#print axioms count0
theorem slot0 : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 0#usize=0#usize := by rfl
#print axioms slot0
theorem slot1 : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 1#usize=1#usize := by rfl
#print axioms slot1
theorem slot2 : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 2#usize=2#usize := by rfl
#print axioms slot2
end AspisR1.JHh_SmallConstants
