import NMX_R3_RawWord64Defs
set_option autoImplicit false
namespace NMX_R3_RawWord64Byte6
open NMX_R3_RawWord64Defs
theorem value (v : Fin 8 → BitVec 8) (i : Nat) (lo : 48 ≤ i) (hi : i < 56) :
 (encoded v).getLsbD i = (folded v).getLsbD i := by
 have positions : i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 := by omega
 rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [encoded, folded, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord64Byte6
