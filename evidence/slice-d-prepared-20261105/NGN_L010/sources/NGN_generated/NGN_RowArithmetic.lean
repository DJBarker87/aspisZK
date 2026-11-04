import NGN_Emitted
set_option autoImplicit false
namespace AspisR1.NGN_RowArithmetic
open Aeneas Aeneas.Std Result
/-- The optimized extraction wraps; the cohort checks. These reached constants
cannot overflow. Normalize these small cells before comparing driver bodies. -/
theorem row30 : lift (U8.wrapping_add 30#u8 1#u8)=(30#u8+1#u8 : Result U8) := by rfl
theorem row31 : lift (U8.wrapping_add 31#u8 1#u8)=(31#u8+1#u8 : Result U8) := by rfl
theorem capacity : lift (Usize.wrapping_add 32#usize 224#usize)=
 (32#usize+224#usize : Result Usize) := by rfl
#print axioms row30
#print axioms row31
#print axioms capacity
end AspisR1.NGN_RowArithmetic
