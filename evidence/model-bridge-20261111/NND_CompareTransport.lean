import NND_RegistryPredicates
import NND_CarrierInjective
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_CompareTransport
open Aeneas Aeneas.Std Result NND_Carrier
attribute [local instance] Classical.propDecidable

theorem key_decide (x y : Array U8 32#usize) :
 decide (key x = key y) = decide (x = y) := by
 apply Bool.eq_iff_iff.mpr
 simp only [decide_eq_true_eq]
 exact key_eq_iff x y

theorem key_ne (x y : Array U8 32#usize) :
 (!(decide (x = y))) = decide (key x ≠ key y) := by
 rw [decide_not,key_decide]

theorem array_ne (x y : Array U8 32#usize) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 x y = ok (decide (key x ≠ key y)) := by
 rw [NGL_ArrayEquality.ne_value,key_ne]

theorem flag_clear (x m : U8) :
 decide (x &&& m = 0#u8) = (byte x &&& byte m == (0 : UInt8)) := by
 apply Bool.eq_iff_iff.mpr
 simp only [decide_eq_true_eq,beq_iff_eq]
 exact (byte_eq_iff (x &&& m) 0#u8).symm

#print axioms key_decide
#print axioms key_ne
#print axioms array_ne
#print axioms flag_clear
end NND_CompareTransport
end
