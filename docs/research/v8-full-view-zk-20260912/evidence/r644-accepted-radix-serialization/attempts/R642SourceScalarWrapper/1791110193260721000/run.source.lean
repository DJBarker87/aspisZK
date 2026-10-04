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
      (w.bv &&& BitVec.zeroExtend 64 ((2147483647 : U32).bv)) =
    BitVec.extractLsb' 0 32 (w.bv &&& (2147483647 : BitVec 64))
  have hword : BitVec.zeroExtend 64 ((2147483647 : U32).bv) =
      (2147483647 : BitVec 64).bv := by
    simp only [U32.ofNat_bv]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by norm_num)
  rw [hword]
  exact (BitVec.setWidth_eq_extractLsb' (by decide)).symm

theorem block_word_matches_maskedLow32
    (b : Array U8 31#usize) (j : Fin 8) :
    (R624DecoderInnerExecution.blockWords
      (R623PackedDecoderExecution.blockValues b))[j.val]!.bv =
      R637PackedBitExtraction.maskedLow32
        (R641PackedByteConcat.word0 b)
        (R641PackedByteConcat.word1 b)
        (R641PackedByteConcat.word2 b)
        (R641PackedByteConcat.word3 b) j := by
  have hvalue :
      (R624DecoderInnerExecution.blockWords
        (R623PackedDecoderExecution.blockValues b))[j.val]! =
        R624DecoderInnerExecution.sourceMaskedValue
          (R623PackedDecoderExecution.blockValues b).val[j.val]'(by
            have hb : (R623PackedDecoderExecution.blockValues b).val.length = 8 :=
              (R623PackedDecoderExecution.blockValues b).property
            simpa [j.isLt] using hb ▸ j.isLt) := by
    simp only [R624DecoderInnerExecution.blockWords, List.getElem!_ofFn]
    simp
  rw [hvalue, mask_cast_bv]
  simp [R623PackedDecoderExecution.blockValues,
    R637PackedBitExtraction.maskedLow32, R637PackedBitExtraction.sourceWords,
    R641PackedByteConcat.word0, R641PackedByteConcat.word1,
    R641PackedByteConcat.word2, R641PackedByteConcat.word3,
    R624DecoderInnerExecution.sourceWordNat]

#print axioms mask_cast_bv
#print axioms block_word_matches_maskedLow32

end AspisV8R19.R642SourceScalarWrapper
