import AspisV8R19.R481NativeQM31Cell
set_option autoImplicit false
namespace AspisV8R19.R637PackedBitExtraction

def packed256 (w0 w1 w2 w3 : BitVec 64) : BitVec 256 := w3 ++ w2 ++ w1 ++ w0

def sourceWords (w0 w1 w2 w3 : BitVec 64) : List (BitVec 64) :=
  [w0, w0 >>> 31, (w0 >>> 62) ||| (w1 <<< 2), w1 >>> 29,
   (w1 >>> 60) ||| (w2 <<< 4), w2 >>> 27,
   (w2 >>> 58) ||| (w3 <<< 6), w3 >>> 25]

def maskedLow32 (w0 w1 w2 w3 : BitVec 64) (j : Fin 8) : BitVec 32 :=
  BitVec.extractLsb' 0 32
    (((sourceWords w0 w1 w2 w3)[j.val]'(by simp [sourceWords])) &&& (2147483647 : BitVec 64))

lemma mask_bit (i : Nat) (hi : i < 32) :
    (2147483647 : BitVec 64).getLsbD i = true := by
  rw [BitVec.getLsbD_ofNat]
  have hm : 2147483647 = 2^31 - 1 := by norm_num
  rw [hm, Nat.testBit_two_pow_sub_one]
  simp [Nat.lt_trans hi]

theorem source_word_masked_extract (w0 w1 w2 w3 : BitVec 64) (j : Fin 8) :
    maskedLow32 w0 w1 w2 w3 j =
      BitVec.zeroExtend 32 (BitVec.extractLsb' (31*j.val) 31 (packed256 w0 w1 w2 w3)) := by
  fin_cases j
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [maskedLow32, sourceWords, packed256, List.getElem_cons_zero,
      List.getElem_cons_succ, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft]
    rw [mask_bit i hi]
    simp only [Bool.and_true]
    omega

#print axioms mask_bit
#print axioms source_word_masked_extract
end AspisV8R19.R637PackedBitExtraction
