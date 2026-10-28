import PV_B3P_FieldBase227
namespace PV_B3P_Zero227
open Aeneas Aeneas.Std PV_B3P_FieldBase227 PV_B3P_227
set_option autoImplicit false

theorem subtract_zero : subtract 0#u32 = 0#u32 := by decide
theorem reduce_zero : reduce 0#u64 = 0#u32 := by decide
theorem add_zero_zero : add 0#u32 0#u32 = 0#u32 := by decide
theorem sub_zero_zero : sub 0#u32 0#u32 = 0#u32 := by decide
theorem mul_zero_zero : mul 0#u32 0#u32 = 0#u32 := by decide

#print axioms subtract_zero
#print axioms reduce_zero
#print axioms add_zero_zero
#print axioms sub_zero_zero
#print axioms mul_zero_zero
end PV_B3P_Zero227
