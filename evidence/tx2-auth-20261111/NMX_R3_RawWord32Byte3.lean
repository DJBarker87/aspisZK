import NMX_R3_RawWord32Defs
set_option autoImplicit false
namespace NMX_R3_RawWord32Byte3
open NMX_R3_RawWord32Defs
theorem value (a b c d : BitVec 8) (i : Nat) (lo : 24 ≤ i) (hi : i < 32) :
 (encoded a b c d).getLsbD i = (assembled a b c d).getLsbD i := by
 have positions : i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
 rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [encoded, assembled, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord32Byte3
