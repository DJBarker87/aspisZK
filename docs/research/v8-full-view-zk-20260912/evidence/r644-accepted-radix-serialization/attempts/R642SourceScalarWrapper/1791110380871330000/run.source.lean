import AspisV8R19.R623PackedDecoderExecution
import AspisV8R19.R624DecoderInnerExecution
import AspisV8R19.R637PackedBitExtraction
import AspisV8R19.R641PackedByteConcat
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R642SourceScalarWrapper

open Aeneas Aeneas.Std

private theorem mask_cast_bv (w : U64) :
    (R624DecoderInnerExecution.sourceMaskedValue w).bv =
      BitVec.extractLsb' 0 32 (w.bv &&& (2147483647 : BitVec 64)) := by
  simp only [R624DecoderInnerExecution.sourceMaskedValue, UScalar.cast, UScalar.and]
  change BitVec.zeroExtend 32
      (w.bv &&& BitVec.zeroExtend 64 (2147483647#u32).bv) =
    BitVec.extractLsb' 0 32 (w.bv &&& (2147483647 : BitVec 64))
  have hword : BitVec.zeroExtend 64 (2147483647#u32).bv =
      (2147483647 : BitVec 64) := by
    change BitVec.setWidth 64 (BitVec.ofNat 32 2147483647) =
      BitVec.ofNat 64 2147483647
    exact BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64)
      (x := 2147483647) (by decide) (by norm_num)
  rw [hword]
  change BitVec.setWidth 32 (w.bv &&& (2147483647 : BitVec 64)) = _
  exact BitVec.setWidth_eq_extractLsb' (v := 64) (w := 32) (by decide)

theorem block_word_matches_maskedLow32
    (b : Array U8 31#usize) (j : Fin 8) :
    (R624DecoderInnerExecution.blockWords
      (R623PackedDecoderExecution.blockValues b))[j.val]!.bv =
      R637PackedBitExtraction.maskedLow32
        (R641PackedByteConcat.word0 b)
        (R641PackedByteConcat.word1 b)
        (R641PackedByteConcat.word2 b)
        (R641PackedByteConcat.word3 b) j := by
  fin_cases j <;>
    simp [Array.make, R624DecoderInnerExecution.blockWords,
      R624DecoderInnerExecution.sourceWordNat,
      R623PackedDecoderExecution.blockValues,
      R637PackedBitExtraction.maskedLow32,
      R637PackedBitExtraction.sourceWords,
      R641PackedByteConcat.word0, R641PackedByteConcat.word1,
      R641PackedByteConcat.word2, R641PackedByteConcat.word3,
      mask_cast_bv]

#print axioms mask_cast_bv
#print axioms block_word_matches_maskedLow32

end AspisV8R19.R642SourceScalarWrapper
