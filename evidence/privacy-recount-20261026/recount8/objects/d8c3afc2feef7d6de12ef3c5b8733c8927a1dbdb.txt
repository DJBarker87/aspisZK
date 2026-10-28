import R1Z.PV_RDCD_Wrapping194
set_option autoImplicit false
namespace R1Z.PV_RDCD_ShiftBound
open Aeneas Aeneas.Std
/-- The call to unchecked_shr satisfies its Rust precondition on every input. -/
theorem mask_bound (rhs : Nat) : rhs &&& (64-1) < 64 := by
  rw [PV_RDCD_Wrapping194.shift_mask]
  exact Nat.mod_lt _ (by decide)
/-- The exact two reached count values also satisfy that precondition. -/
theorem literal_bounds : (1 : Nat) < 64 ∧ (31 : Nat) < 64 := by decide
#print axioms mask_bound
#print axioms literal_bounds
end R1Z.PV_RDCD_ShiftBound
