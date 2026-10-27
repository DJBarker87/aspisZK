import LPk_Result
set_option autoImplicit false
namespace LPk_Modular
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
#print axioms no_wrap
#print axioms lift_identity
end LPk_Modular
