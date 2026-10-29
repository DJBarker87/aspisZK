import LPk_Step
set_option autoImplicit false
namespace NDH_Arithmetic
open AspisR1.SamplerMachineBounds
theorem no_wrap {q r : Nat} (hq : q < B) (hr : r < P) :
    q * P + r < 2^64 := by
  have h := AspisR1.SamplerLongDivision.dividend_lt_mul
    P_pos B_pos hq hr
  change q * P + r < B * P at h
  have hb : B * P < 2^64 := by norm_num [B,P]
  exact h.trans hb

theorem lift_identity {rem limb q r : Nat}
    (hq : q < B) (hr : r < P) (hrem : rem < P) (hlimb : limb < B)
    (hword : (q*P+r) % 2^64 = (rem*B+limb) % 2^64) :
    LPk_Step.Relation rem limb q r := by
  refine ⟨?_,hr⟩
  have hn : rem*B+limb < 2^64 :=
    (dividend_lt_two63 hrem hlimb).trans (by norm_num)
  simpa only [Nat.mod_eq_of_lt (no_wrap hq hr),Nat.mod_eq_of_lt hn] using hword
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
  exact lift_identity hq hr hrem hl he

open AspisR1.SamplerWord

theorem native_pack (r : UInt64) (d : UInt32) (hr : r.toNat < P) :
    (machineWord r d).toNat = r.toNat * B + d.toNat :=
  machineWord_toNat d hr

#print axioms no_wrap
#print axioms lift_identity
#print axioms product
#print axioms shift_no_wrap
#print axioms subtract_no_wrap
#print axioms relation
#print axioms native_pack
end NDH_Arithmetic
