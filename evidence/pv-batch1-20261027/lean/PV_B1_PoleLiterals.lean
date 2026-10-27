import Aeneas
set_option autoImplicit false
namespace PV_B1_PoleLiterals
open Aeneas Aeneas.Std

theorem zero : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  change (0+1)%UScalar.size .Usize=1
  exact Nat.mod_eq_of_lt (show 1<UScalar.size .Usize from (1#usize : Usize).hSize)

theorem one : Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  change (1+1)%UScalar.size .Usize=2
  exact Nat.mod_eq_of_lt (show 2<UScalar.size .Usize from (2#usize : Usize).hSize)
#print axioms zero
#print axioms one
end PV_B1_PoleLiterals
