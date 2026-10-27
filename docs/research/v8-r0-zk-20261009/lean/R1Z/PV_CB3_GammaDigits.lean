import R1Z.PV_CB3_SamplerCarry
import R1Z.PV_CB3_GammaWrap
namespace R1Z.PV_CB3_GammaDigits
open PV_CB3_SamplerCarry
set_option autoImplicit false

/-- The sampler's two carry passes, retaining the source wrap test. -/
def finish (base : Nat) (digits : List Nat) (high : Nat) : List Nat :=
  let first := addCarry base digits (high + 1)
  if first.2 = 0 then first.1 else (addCarry base first.1 1).1

theorem finish_length (base : Nat) (digits : List Nat) (high : Nat) :
    (finish base digits high).length = digits.length := by
  dsimp only [finish]
  split <;> simp only [length_preserved]

theorem finish_canonical (base : Nat) (positive : 0 < base)
    (digits : List Nat) (high : Nat) :
    ∀ d, d ∈ finish base digits high → d < base := by
  dsimp only [finish]
  split
  · exact digits_canonical base positive digits (high + 1)
  · exact digits_canonical base positive _ 1

/-- Exact arithmetic of both source branches, including the wrap increment. -/
theorem finish_value (base : Nat) (positive : 0 < base)
    (digits : List Nat) (high : Nat)
    (canonical : ∀ d, d ∈ digits → d < base)
    (high_bound : high < base ^ digits.length - 1) :
    value base (finish base digits high) =
      if value base digits + high + 1 < base ^ digits.length
      then value base digits + high + 1
      else value base digits + high + 2 - base ^ digits.length := by
  have low_bound := value_lt_pow base digits canonical
  have first_rem := digits_remainder base positive digits (high + 1)
  have first_carry := carry_quotient base positive digits (high + 1)
  have power_pos := Nat.pow_pos positive (n := digits.length)
  dsimp only [finish]
  rw [← first_carry]
  by_cases small : value base digits + high + 1 < base ^ digits.length
  · have hz : (value base digits + (high + 1)) / base ^ digits.length = 0 :=
      Nat.div_eq_of_lt (by omega)
    rw [hz, if_pos rfl, if_pos small, ← first_rem, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hq : (value base digits + (high + 1)) / base ^ digits.length = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hq, if_neg (by decide : ¬ (1 : Nat) = 0), if_neg small]
    rw [← digits_remainder base positive _ 1, length_preserved, ← first_rem]
    have hr : (value base digits + (high + 1)) % base ^ digits.length =
        value base digits + (high + 1) - base ^ digits.length := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hr, Nat.mod_eq_of_lt (by omega)]
    omega

#print axioms finish_length
#print axioms finish_canonical
#print axioms finish_value
end R1Z.PV_CB3_GammaDigits
