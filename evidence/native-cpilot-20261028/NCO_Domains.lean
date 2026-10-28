import NCO_ScalarBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Domains

/-- The real row-25 shape contradicts the one-window diagnostic contracts. -/
theorem row25 : AspisS1NativeCompact.r1_wire.row_shape 25#u8 =
    ok (some (4#u8, 3712#usize)) := by
  rw [← NCO_ScalarBridge.row_shape]
  rfl

theorem row25_not_validator_window : (3712 : Nat) ≠ 32 := by omega

theorem row25_not_expansion_window :
    (3712 : Nat) / 2 = 1856 ∧ (1856 : Nat) ≠ 16 ∧ (3712 : Nat) ≠ 32 := by omega

theorem row25_not_parser_diagnostic : ¬ (25 < (14 : Nat)) := by omega

#print axioms row25
#print axioms row25_not_validator_window
#print axioms row25_not_expansion_window
#print axioms row25_not_parser_diagnostic
end NCO_Domains
