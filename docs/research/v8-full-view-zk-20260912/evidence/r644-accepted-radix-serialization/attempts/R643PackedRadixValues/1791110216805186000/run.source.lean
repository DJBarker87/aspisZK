import AspisV8R19.R641PackedByteConcat
set_option autoImplicit false
namespace AspisV8R19.R643PackedRadixValues
open Aeneas Aeneas.Std
open R637PackedBitExtraction R641PackedByteConcat

/-- Mathematical base-2^31 digits of the entire 31-byte little-endian block.
The digit P is still a possible representation here; actual acceptance is
required separately to exclude it. -/
def radixDigit (b : Array U8 31#usize) (j : Fin 8) : Nat :=
  (chunkBits248 b).toNat / 2^(31*j.val) % 2^31

theorem masked_source_radix (b : Array U8 31#usize) (j : Fin 8) :
    (maskedLow32 (word0 b) (word1 b) (word2 b) (word3 b) j).toNat =
      radixDigit b j := by
  rw [source_word_masked_extract, packed_bytes_concat]
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le (by decide)]
  rw [BitVec.extractLsb'_toNat]
  unfold bytePack256 radixDigit
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le (by decide)]
  rw [Nat.shiftRight_eq_div_pow]

#print axioms radixDigit
#print axioms masked_source_radix
end AspisV8R19.R643PackedRadixValues
