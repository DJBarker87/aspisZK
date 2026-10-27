import LPi_TowerValues
set_option autoImplicit false
namespace AspisR1.LPm_StubBounds

/-- The caller stub's reference formulas use wrapping word instructions only
to remove redundant verifier-side overflow obligations. These shape bounds
show they still denote the SAME natural-number formulas on canonical inputs. -/
theorem product (a b : Nat) (ha : a<4294967296) (hb : b<4294967296) :
    a*b<18446744073709551616 := by
  have h := Nat.mul_le_mul (show a≤4294967295 by omega) (show b≤4294967295 by omega)
  norm_num at h
  omega

theorem canonical_sum (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
    a+b<4294967296 ∧ a+2147483647<4294967296 ∧ b≤a+2147483647 := by omega

theorem residue (n : Nat) : n%2147483647<2147483647 := Nat.mod_lt _ (by decide)

#print axioms product
#print axioms canonical_sum
#print axioms residue
end AspisR1.LPm_StubBounds
