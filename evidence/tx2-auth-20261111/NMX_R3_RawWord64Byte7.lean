import NMX_R3_RawWord64Defs
set_option autoImplicit false
namespace NMX_R3_RawWord64Byte7
open NMX_R3_RawWord64Defs
theorem value (v : Fin 8 → BitVec 8) (i : Nat) (lo : 56 ≤ i) (hi : i < 64) :
 (encoded v).getLsbD i = (folded v).getLsbD i := by
 have positions : i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
 rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [encoded, folded, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord64Byte7
