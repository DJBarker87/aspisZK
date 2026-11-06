import Port5Q2_ReaderValidate
import NJC_ValidateEmission
set_option autoImplicit false
namespace NJC_ValidateArithmetic
open Aeneas Aeneas.Std Result AspisR1
/-- The freshly emitted checked shift at the actual literal count. The existing
wrapping shift uses its BitVec closed form; no large recurrence is reduced. -/
theorem shift : (1#u32 <<< 18#i32 : Result U32)=ok 262144#u32 := by
 rfl

theorem increment (i : Usize) (small : i.val<22) :
 (i+1#usize : Result Usize)=ok (Usize.wrapping_add i 1#usize) :=
 Port3_Wrapping.checked_add i 1#usize (by change i.val+1≤4096;omega)
#print axioms shift
#print axioms increment
end NJC_ValidateArithmetic
