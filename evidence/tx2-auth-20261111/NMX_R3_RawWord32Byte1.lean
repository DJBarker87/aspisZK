import NMX_R3_RawWord32Defs
set_option autoImplicit false
namespace NMX_R3_RawWord32Byte1
open NMX_R3_RawWord32Defs
theorem value (a b c d : BitVec 8) (i : Nat) (lo : 8 ≤ i) (hi : i < 16) :
 (encoded a b c d).getLsbD i = (assembled a b c d).getLsbD i := by
 have positions : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
 rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [encoded, assembled, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord32Byte1
