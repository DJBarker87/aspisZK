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
    by_cases h1a : i - 64 < 64
    · have h128 : i < 128 := by omega
      simp [h0, h1a, h128]
    · have h128 : ¬ i < 128 := by omega
      simp only [h0, h128, if_false, if_neg h1a]
      rw [BitVec.getLsbD_append]
      by_cases h2a : i - 64 - 64 < 64
      · have h192 : i < 192 := by omega
        simp only [h0, h128, h1a, h2a, h192, if_true]
        rw [show i - 64 - 64 = i - 128 by omega]
      · have h192 : ¬ i < 192 := by omega
        simp only [h0, h128, h1a, h2a, h192, if_false]
        rw [show i - 64 - 64 - 64 = i - 192 by omega]


lemma source_word_bit (w0 w1 w2 w3 : BitVec 64) (j : Fin 8) (i : Nat) (hi : i < 31) :
    ((sourceWords w0 w1 w2 w3)[j.val]'(by simp [sourceWords])).getLsbD i =
      (packed256 w0 w1 w2 w3).getLsbD (31*j.val+i) := by
  fin_cases j
  · simp only [sourceWords, List.getElem_cons_zero]
    have h0 : i < 64 := by omega
    rw [packed_lsbD]
    simp [h0]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight]
    have h0 : 31+i < 64 := by omega
    rw [packed_lsbD]
    simp [h0]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases h2 : i < 2
    · have hp : 31*2+i < 64 := by omega
      rw [packed_lsbD]
      simp [hp, h2]
    · have hp0 : ¬ 31*2+i < 64 := by omega
      have hp1 : 31*2+i < 128 := by omega
      have hout : 64 ≤ 62+i := by omega
      have hidx : 62+i-64 = i-2 := by omega
      rw [packed_lsbD]
      rw [if_neg hp0, if_pos hp1, hidx]
      have hi64 : i < 64 := by omega
      simp [h2, hi64, getLsbD_false_of_ge w0 hout]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight]
    have hp0 : ¬ 31*3+i < 64 := by omega
    have hp1 : 31*3+i < 128 := by omega
    have hidx : 31*3+i-64 = 29+i := by omega
    rw [packed_lsbD, if_neg hp0, if_pos hp1, hidx]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases h4 : i < 4
    · have hp0 : ¬ 31*4+i < 64 := by omega
      have hp1 : 31*4+i < 128 := by omega
      have hidx : 31*4+i-64 = 60+i := by omega
      rw [packed_lsbD, if_neg hp0, if_pos hp1, hidx]
      simp [h4]
    · have hp0 : ¬ 31*4+i < 64 := by omega
      have hp1 : ¬ 31*4+i < 128 := by omega
      have hp2 : 31*4+i < 192 := by omega
      have hout : 64 ≤ 60+i := by omega
      have hidx : 31*4+i-128 = i-4 := by omega
      rw [packed_lsbD, if_neg hp0, if_neg hp1, if_pos hp2, hidx]
      have hi64 : i < 64 := by omega
      simp [h4, hi64, getLsbD_false_of_ge w1 hout]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight]
    have hp0 : ¬ 31*5+i < 64 := by omega
    have hp1 : ¬ 31*5+i < 128 := by omega
    have hp2 : 31*5+i < 192 := by omega
    have hidx : 31*5+i-128 = 27+i := by omega
    rw [packed_lsbD, if_neg hp0, if_neg hp1, if_pos hp2, hidx]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases h6 : i < 6
    · have hp0 : ¬ 31*6+i < 64 := by omega
      have hp1 : ¬ 31*6+i < 128 := by omega
      have hp2 : 31*6+i < 192 := by omega
      have hidx : 31*6+i-128 = 58+i := by omega
      rw [packed_lsbD, if_neg hp0, if_neg hp1, if_pos hp2, hidx]
      simp [h6]
    · have hp0 : ¬ 31*6+i < 64 := by omega
      have hp1 : ¬ 31*6+i < 128 := by omega
      have hp2 : ¬ 31*6+i < 192 := by omega
      have hout : 64 ≤ 58+i := by omega
      have hidx : 31*6+i-192 = i-6 := by omega
      rw [packed_lsbD, if_neg hp0, if_neg hp1, if_neg hp2, hidx]
      have hi64 : i < 64 := by omega
      simp [h6, hi64, getLsbD_false_of_ge w2 hout]
  · simp only [sourceWords, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.getLsbD_ushiftRight]
    have hp0 : ¬ 31*7+i < 64 := by omega
    have hp1 : ¬ 31*7+i < 128 := by omega
    have hp2 : ¬ 31*7+i < 192 := by omega
    have hidx : 31*7+i-192 = 25+i := by omega
    rw [packed_lsbD, if_neg hp0, if_neg hp1, if_neg hp2, hidx]

lemma source_word_masked_extract (w0 w1 w2 w3 : BitVec 64) (j : Fin 8) :
    maskedLow32 w0 w1 w2 w3 j =
      BitVec.zeroExtend 32 (BitVec.extractLsb' (31*j.val) 31 (packed256 w0 w1 w2 w3)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [maskedLow32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth]
  rw [Nat.zero_add, mask_bit]
  by_cases h31 : i < 31
  · rw [source_word_bit w0 w1 w2 w3 j i h31]
    simp [h31, hi]
  · simp [h31, hi]

#print axioms source_word_masked_extract
#print axioms source_word_bit
#print axioms packed_lsbD
#print axioms mask_bit
#print axioms getLsbD_false_of_ge
end AspisV8R19.R637PackedBitExtraction
