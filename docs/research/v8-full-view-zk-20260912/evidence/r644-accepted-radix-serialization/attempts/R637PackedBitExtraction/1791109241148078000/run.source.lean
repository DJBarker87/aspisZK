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

lemma mask_bit (i : Nat) :
    (2147483647 : BitVec 64).getLsbD i = decide (i < 31) := by
  change (BitVec.ofNat 64 2147483647).getLsbD i = decide (i < 31)
  rw [BitVec.getLsbD_ofNat]
  have hm : 2147483647 = 2^31 - 1 := by norm_num
  rw [hm, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 31 <;> simp [h] <;> omega

lemma getLsbD_false_of_ge {n : Nat} (x : BitVec n) {i : Nat} (h : n ≤ i) :
    x.getLsbD i = false := by
  change x.toNat.testBit i = false
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)

lemma packed_lsbD (w0 w1 w2 w3 : BitVec 64) (i : Nat) :
    (packed256 w0 w1 w2 w3).getLsbD i =
      if i < 64 then w0.getLsbD i else
      if i < 128 then w1.getLsbD (i - 64) else
      if i < 192 then w2.getLsbD (i - 128) else w3.getLsbD (i - 192) := by
  change (w3 ++ w2 ++ w1 ++ w0).getLsbD i = _
  rw [BitVec.getLsbD_append]
  by_cases h0 : i < 64
  · simp [h0]
  · simp only [if_neg h0]
    rw [BitVec.getLsbD_append]
    by_cases h1 : i < 128
    · have h1' : i - 64 < 64 := by omega
      simp [h0, h1, h1']
    · simp only [h0, h1, if_false]
      rw [BitVec.getLsbD_append]
      by_cases h2 : i < 192
      · have h2' : i - 128 < 64 := by omega
        simp [h0, h1, h2, h2']
      · have h2' : ¬ i - 128 < 64 := by omega
        simp only [h0, h1, h2, h2', if_false]
        congr 1 <;> omega


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
    simp only [Nat.zero_add, mask_bit]
    by_cases h31 : i < 31
    · simp [h31, hi, BitVec.getLsbD_or]
      repeat rw [BitVec.getLsbD_append]
      split_ifs <;> simp_all <;> first | rfl | (congr 1 <;> omega) | omega
    · simp [h31, hi]

#print axioms packed_lsbD
#print axioms mask_bit
#print axioms getLsbD_false_of_ge
#print axioms source_word_masked_extract
end AspisV8R19.R637PackedBitExtraction
