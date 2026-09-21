import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Bounds for the natural-number intermediates of the staged DIF butterfly.
Canonical source limbs are premises. This is not source reducer correctness,
Rust extraction, FFT equivalence or privacy. -/
set_option autoImplicit false
namespace AspisV8R17.DifButterfly

theorem padded_difference (u v : Nat) (hu : u < 2147483647)
    (hv : v < 2147483647) :
    v ≤ u+2147483647 ∧ u+2147483647 < 18446744073709551616 ∧
    u+2147483647-v ≤ 4294967293 := by omega

theorem wide_product (x w : Nat) (hx : x ≤ 4294967293)
    (hw : w < 2147483647) : x*w ≤ 9223372021822390278 := by
  have h := Nat.mul_le_mul hx (show w ≤ 2147483646 by omega)
  norm_num at h
  exact h

/-- Includes the intermediate real addition before subtraction. -/
theorem raw_bounds (a b c d : Nat)
    (ha : a ≤ 9223372021822390278) (hb : b ≤ 9223372021822390278)
    (hc : c ≤ 9223372021822390278) (hd : d ≤ 9223372021822390278) :
    b ≤ a+2*4611686014132420609 ∧
    a+2*4611686014132420609 < 18446744073709551616 ∧
    a+2*4611686014132420609-b < 4*4611686014132420609 ∧
    c+d < 4*4611686014132420609 ∧
    c+d < 18446744073709551616 := by omega

#print axioms padded_difference
#print axioms wide_product
#print axioms raw_bounds
end AspisV8R17.DifButterfly
