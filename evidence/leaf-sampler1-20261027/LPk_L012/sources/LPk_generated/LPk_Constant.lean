import LPk_Chunks
set_option autoImplicit false
namespace LPk_Constant
open AspisR1.SamplerMachineBounds
/-- Sparse form of the constant product, independent of native division. -/
theorem product (q : Nat) : q * P = q * 2^31 - q := by
  rw [P,Nat.mul_sub,Nat.mul_one]

theorem shift_no_wrap {q : Nat} (hq : q < B) : q * 2^31 < 2^64 := by
  have h := Nat.mul_lt_mul_of_pos_right hq (show 0 < 2^31 by norm_num)
  have hb : B * 2^31 < 2^64 := by norm_num [B]
  exact h.trans hb

theorem subtract_no_wrap (q : Nat) : q ≤ q * 2^31 := by
  have h : q * 1 ≤ q * 2^31 := Nat.mul_le_mul_left q (by norm_num)
  simpa only [Nat.mul_one] using h

/-- The sparse word identity is exactly the required relation after the
independently checked quotient/remainder bounds. -/
theorem relation {rem limb q r : Nat} (hrem : rem < P) (hl : limb < B)
    (hq : q < B) (hr : r < P)
    (he : ((q*2^31-q)+r) % 2^64 = (rem*B+limb) % 2^64) :
    LPk_Step.Relation rem limb q r := by
  rw [← product q] at he
  exact LPk_Modular.lift_identity hq hr hrem hl he
#print axioms product
#print axioms shift_no_wrap
#print axioms subtract_no_wrap
#print axioms relation
end LPk_Constant
