import PV_L2E_ByteWord
set_option autoImplicit false
namespace PV_L2E_QueryMask

/-- The shipped literal mask is the same operation as the scanner model's
remainder. This closes the bitwise/natural-number distinction for every word. -/
theorem mask_is_remainder (w : Nat) : (w &&& 262143)=w%262144 := by
  change (w &&& (2^18-1))=w%2^18
  exact Nat.and_two_pow_sub_one_eq_mod w 18

theorem bounded (w : Nat) : (w &&& 262143)<2^18 := by
  rw [mask_is_remainder]
  exact Nat.mod_lt _ (by decide)

#print axioms mask_is_remainder
#print axioms bounded
end PV_L2E_QueryMask
