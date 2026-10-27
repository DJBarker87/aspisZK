import R1Z.PV_CB3_SamplerCarry
namespace R1Z.PV_CB3_RankBound
open PV_CB3_SamplerCarry
set_option autoImplicit false

/-- A symbolic word/base comparison bounds the high quotient without reducing
large concrete powers. This applies before any sampler carry operation. -/
theorem high_lt_base (base radix factor : Nat) (positive : 0 < base)
    (words : List Nat) (canonical : ∀ d, d ∈ words → d < radix)
    (radix_bound : radix ≤ base * factor) (factor_bound : factor ^ words.length ≤ base) :
    value radix words / base ^ words.length < base := by
  have hv := value_lt_pow radix words canonical
  have hp := Nat.pow_le_pow_left radix_bound words.length
  rw [Nat.mul_pow] at hp
  have hb := Nat.mul_le_mul_left (base ^ words.length) factor_bound
  have upper : value radix words < base * base ^ words.length := by
    rw [Nat.mul_comm]
    omega
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos positive)).2 upper

#print axioms high_lt_base
end R1Z.PV_CB3_RankBound
