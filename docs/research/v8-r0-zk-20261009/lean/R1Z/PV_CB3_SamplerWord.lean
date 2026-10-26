import Std
namespace R1Z.PV_CB3_SamplerWord
set_option autoImplicit false

/-- The selected sampler's base and machine-word radix. -/
def base : Nat := 2147483647
def radix : Nat := 4294967296

def dividend (remainder word : Nat) : Nat := remainder * radix + word

/-- The full long-division dividend is below base·2^32. This shape bound
precedes any finite-word native gate or recurrence evaluation. -/
theorem dividend_bound (remainder word : Nat)
    (hr : remainder < base) (hw : word < radix) :
    dividend remainder word < base * radix := by
  unfold dividend base radix at *
  omega

theorem quotient_word_bound (remainder word : Nat)
    (hr : remainder < base) (hw : word < radix) :
    dividend remainder word / base < radix := by
  have hb : 0 < base := by unfold base; omega
  apply (Nat.div_lt_iff_lt_mul hb).2
  simpa only [Nat.mul_comm] using dividend_bound remainder word hr hw

theorem canonical_remainder (remainder word : Nat) :
    dividend remainder word % base < base := by
  apply Nat.mod_lt
  unfold base
  omega

/-- Exact conservation, rather than merely a range or successful-fixture fact. -/
theorem division_identity (remainder word : Nat) :
    dividend remainder word % base + base * (dividend remainder word / base) =
      dividend remainder word := Nat.mod_add_div _ _

theorem dividend_u64_bound (remainder word : Nat)
    (hr : remainder < base) (hw : word < radix) :
    dividend remainder word < radix * radix := by
  unfold dividend base radix at *
  omega

#print axioms dividend_bound
#print axioms quotient_word_bound
#print axioms canonical_remainder
#print axioms division_identity
#print axioms dividend_u64_bound
end R1Z.PV_CB3_SamplerWord
