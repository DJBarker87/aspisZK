import NMX_R3_RawWord32Defs
set_option autoImplicit false
namespace NMX_R3_RawWord32Byte2
open NMX_R3_RawWord32Defs
theorem value (a b c d : BitVec 8) (i : Nat) (lo : 16 ≤ i) (hi : i < 24) :
 (encoded a b c d).getLsbD i = (assembled a b c d).getLsbD i := by
 have positions : i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by omega
 rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [encoded, assembled, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord32Byte2
