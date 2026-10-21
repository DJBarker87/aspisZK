import Aeneas
import R1RetainedFieldByteCodec

/-! Symbolic four-byte agreement for the actual Aeneas U32 primitive and the
unchanged retained byte decoder. No parser or field assumption is required. -/
namespace AspisR1.ExtractedRecordByteValue
open Aeneas Aeneas.Std

/-- Four symbolic byte ranges; no native decision procedure is used. -/
private theorem le4_bits (b0 b1 b2 b3 : BitVec 8) :
    BitVec.fromLEBytes [b0,b1,b2,b3] = ((b3 ++ b2) ++ b1) ++ b0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hi32 : i < 32 := hi
  rw [BitVec.fromLEBytes_getElem]
  erw [BitVec.getElem_append]
  by_cases h0 : i < 8
  · have hd : i / 8 = 0 := by omega
    have hm : i % 8 = i := by omega
    simp [hd, hm, h0, BitVec.getElem_eq_testBit_toNat, Byte.testBit]
  · simp only [h0, ↓reduceDIte]
    erw [BitVec.getElem_append]
    by_cases h1 : i - 8 < 8
    · have hd : i / 8 = 1 := by omega
      have hm : i % 8 = i - 8 := by omega
      simp [hd, hm, h1, BitVec.getElem_eq_testBit_toNat, Byte.testBit]
    · simp only [h1, ↓reduceDIte]
      erw [BitVec.getElem_append]
      by_cases h2 : i - 8 - 8 < 8
      · have hd : i / 8 = 2 := by omega
        have hm : i % 8 = i - 8 - 8 := by omega
        simp [hd, hm, h2, BitVec.getElem_eq_testBit_toNat, Byte.testBit]
      · have hd : i / 8 = 3 := by omega
        have hm : i % 8 = i - 8 - 8 - 8 := by omega
        simp [hd, hm, h2, BitVec.getElem_eq_testBit_toNat, Byte.testBit]

private theorem append_byte_value {n : Nat} (high : BitVec n) (low : BitVec 8) :
    (high ++ low).toNat = high.toNat * 256 + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt]
  rw [Nat.shiftLeft_eq]

/-- Exact mathematical value of the primitive called in parser headers and
canonical 32-byte field chunks. -/
theorem from_le4_value (b0 b1 b2 b3 : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3])).val =
      b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * b3.val := by
  change (BitVec.fromLEBytes [b0.bv,b1.bv,b2.bv,b3.bv]).toNat =
    b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * b3.val
  rw [le4_bits, append_byte_value, append_byte_value, append_byte_value]
  change ((b3.val * 256 + b2.val) * 256 + b1.val) * 256 + b0.val = _
  omega

def rawByte (byte : U8) : RetainedFieldByteCodec.Byte := byte.bv.toFin

theorem decodeWordLE_agreement (b0 b1 b2 b3 : U8) :
    RetainedFieldByteCodec.decodeWordLE ![rawByte b0,rawByte b1,rawByte b2,rawByte b3] =
      (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3])).bv.toFin := by
  apply Fin.ext
  change b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * b3.val = _
  exact (from_le4_value b0 b1 b2 b3).symm

end AspisR1.ExtractedRecordByteValue

#print axioms AspisR1.ExtractedRecordByteValue.from_le4_value
#print axioms AspisR1.ExtractedRecordByteValue.decodeWordLE_agreement
