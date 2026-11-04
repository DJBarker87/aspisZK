import NGN_Emitted
set_option autoImplicit false
namespace AspisR1.NGN_RowArithmetic
open Aeneas Aeneas.Std Result WP
/-- The optimized extraction wraps; the cohort checks. These reached constants
cannot overflow. Normalize these small cells before comparing driver bodies. -/
theorem row30 : lift (U8.wrapping_add 30#u8 1#u8)=(30#u8+1#u8 : Result U8) := by rfl
theorem row31 : lift (U8.wrapping_add 31#u8 1#u8)=(31#u8+1#u8 : Result U8) := by rfl
theorem capacity : lift (Usize.wrapping_add 32#usize 224#usize)=
 (32#usize+224#usize : Result Usize) := by
 have spec : (32#usize+224#usize : Result Usize) ⦃ out => out.val=256 ⦄ := by
  step*
  scalar_tac
 obtain ⟨out,checked,value⟩ := WP.spec_imp_exists spec
 rw [checked]
 change ok (Usize.wrapping_add 32#usize 224#usize)=ok out
 congr 1
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_add_val_eq,value]
 change 256 % UScalar.size .Usize=256
 apply Nat.mod_eq_of_lt
 rw [UScalar.size_def]
 scalar_tac
#print axioms row30
#print axioms row31
#print axioms capacity
end AspisR1.NGN_RowArithmetic
