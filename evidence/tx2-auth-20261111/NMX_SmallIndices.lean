import NGL_DistinctInduction
set_option autoImplicit false
namespace NMX_SmallIndices
open Aeneas Aeneas.Std
theorem add0 : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 0#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add0
theorem add1 : Usize.wrapping_add 1#usize 1#usize = 2#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 1#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add1
theorem add2 : Usize.wrapping_add 2#usize 1#usize = 3#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 2#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add2
theorem add3 : Usize.wrapping_add 3#usize 1#usize = 4#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 3#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add3
theorem add4 : Usize.wrapping_add 4#usize 1#usize = 5#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 4#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add4
theorem add5 : Usize.wrapping_add 5#usize 1#usize = 6#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 5#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add5
theorem add6 : Usize.wrapping_add 6#usize 1#usize = 7#usize := by
 apply UScalar.eq_of_val_eq
 rw [NFQ_ZeroPrimitives.wrap_add 6#usize 1#usize (by scalar_tac)]
 rfl
#print axioms add6
end NMX_SmallIndices
