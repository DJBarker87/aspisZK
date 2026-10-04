import AspisV8R19.R623PackedDecoderExecution

set_option autoImplicit false

namespace AspisV8R19.R639PackedByteBits

open Aeneas Aeneas.Std
open AspisV8R19.R623PackedDecoderExecution

/-- Little-endian bit order for one source-shaped eight-byte word. -/
theorem eight_from_le_bytes_bit
    (b : Array U8 31#usize) (off : Nat) (hoff : off ≤ 23) (bit : Nat) (hbit : bit < 64) :
    (core.num.U64.from_le_bytes (eight b off hoff)).bv.getLsbD bit =
      (b.val[off + bit / 8]'(by
        have hb : b.val.length = 31 := b.property
        omega)).bv.getLsbD (bit % 8) := by
  change (BitVec.fromLEBytes ((eight b off hoff).val.map U8.bv)).toNat.testBit bit = _
  rw [← BitVec.getElem!_eq_testBit_toNat]
  rw [BitVec.fromLEBytes_getElem!]
  have hq : bit / 8 < 8 := by omega
  have hb : b.val.length = 31 := b.property
  have hp : off + bit / 8 < b.val.length := by omega
  simp [eight, hq, BitVec.getLsbD]
  rw [List.getD_getElem?]
  have hp31 : off + bit / 8 < 31 := by omega
  simp [hp31]

#print axioms eight_from_le_bytes_bit
end AspisV8R19.R639PackedByteBits
