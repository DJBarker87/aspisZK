import Std
set_option autoImplicit false
namespace R1Z.PV_RW_SamplerLimbBounds

def p : Nat := 2147483647

theorem positive : 0 < p := by unfold p; omega

theorem dividend_bound (remainder word : Nat) (hr : remainder < p)
    (hw : word < 4294967296) :
    remainder * 4294967296 + word < 9223372036854775808 := by
  unfold p at hr
  omega

theorem dividend_fits (remainder word : Nat) (hr : remainder < p)
    (hw : word < 4294967296) :
    remainder * 4294967296 + word < 18446744073709551616 := by
  have small := dividend_bound remainder word hr hw
  omega

theorem remainder_preserved (dividend : Nat) : dividend % p < p :=
  Nat.mod_lt _ positive

theorem prefix_bound (consumed : Nat) (h : consumed ≤ 8) :
    consumed+1 < 10 ∧ (consumed < 8 → 7-consumed < 8) := by omega
#print axioms positive
#print axioms dividend_bound
#print axioms dividend_fits
#print axioms remainder_preserved
#print axioms prefix_bound
end R1Z.PV_RW_SamplerLimbBounds
