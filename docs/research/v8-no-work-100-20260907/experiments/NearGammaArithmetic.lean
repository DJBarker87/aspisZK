import Mathlib.Data.Nat.Choose.Basic

/-! Small exact arithmetic inputs to the symbolic near-gamma theorems. -/
set_option autoImplicit false
namespace AspisV8.NearGammaArithmetic

theorem support_certificate :
    9557 * Nat.choose 64 29 < 113328 * Nat.choose 61 29 := by decide

theorem own_support_mismatch_cap : 64*9301 < 36*16536 := by decide

theorem own_support_count : 262144-16535 = 245609 := by decide

theorem own_support_symbol_count : 4*245609 = 982436 := by decide

#print axioms support_certificate
#print axioms own_support_mismatch_cap
#print axioms own_support_count
#print axioms own_support_symbol_count
end AspisV8.NearGammaArithmetic
