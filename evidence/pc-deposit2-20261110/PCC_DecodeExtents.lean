import PCC_DepositDecodeReference
set_option autoImplicit false
namespace PCC
open PCA
/-- All fixed slices are in bounds after the FIRST source length check.
No successful parse or successful conversion premise is needed. -/
theorem decode_extents (bytes : Bytes) (length : 80 ≤ bytes.length) :
    ((bytes.drop 6).take 2).length = 2 ∧
    ((bytes.drop 8).take 32).length = 32 ∧
    ((bytes.drop 40).take 4).length = 4 ∧
    ((bytes.drop 44).take 4).length = 4 ∧
    ((bytes.drop 48).take 32).length = 32 := by
  simp only [List.length_take, List.length_drop]
  omega

/-- The decoded u16 length is checked before usize addition in the source. -/
theorem payload_add_fits (declared : Nat) (h : declared ≤ 512) :
    80 + declared ≤ 592 ∧ 80 + declared < 2^64 := by omega
#print axioms decode_extents
#print axioms payload_add_fits
end PCC
