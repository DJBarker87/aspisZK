import Aeneas
set_option autoImplicit false
namespace LPt_LPl_G
/-- Every iteration's source window is contained in the caller's full buffer. -/
theorem window_contained (width count i : Nat) (hi : i < count) :
    width * i + width ≤ width * count := by
  have h := Nat.mul_le_mul_left width (Nat.succ_le_iff.mpr hi)
  simpa only [Nat.mul_succ] using h
/-- Covers arbitrary rows of the 29-value scanner, rather than 29 fixtures. -/
theorem scan928 (i : Nat) (hi : i < 29) : 32*i+32 ≤ 928 := by omega
/-- The 116-value validator and late Claims decoder use this same range. -/
theorem record3712 (i : Nat) (hi : i < 116) : 32*i+32 ≤ 3712 := by omega
/-- Late decode windows remain in the SAME record for all three Claims offsets. -/
theorem claims_window (point i : Nat) (hp : point < 3) (hi : i < 29) :
    29*point+i < 116 ∧ 5+32*(29*point+i)+16 ≤ 5+116*32 := by omega
#print axioms window_contained
#print axioms scan928
#print axioms record3712
#print axioms claims_window
end LPt_LPl_G
