import NMX_R3_RawWord64Defs
set_option autoImplicit false
namespace NMX_R3_RawWord64Byte0
open NMX_R3_RawWord64Defs
theorem value (v : Fin 8 → BitVec 8) (i : Nat) (lo : 0 ≤ i) (hi : i < 8) :
 (encoded v).getLsbD i = (folded v).getLsbD i := by
 have positions : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
 rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [encoded, folded, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord64Byte0
