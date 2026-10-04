import AspisV8R19.R481NativeQM31Cell

set_option autoImplicit false
namespace AspisV8R19.R637PackedBitExtraction

def packed256 (w0 w1 w2 w3 : BitVec 64) : BitVec 256 := w3 ++ w2 ++ w1 ++ w0

/-- The eight exact extraction expressions from one packed 31-byte block. -/
def sourceWords (w0 w1 w2 w3 : BitVec 64) : List (BitVec 64) :=
  [ w0,
    w0 >>> 31,
    (w0 >>> 62) ||| (w1 <<< 2),
    w1 >>> 29,
    (w1 >>> 60) ||| (w2 <<< 4),
    w2 >>> 27,
    (w2 >>> 58) ||| (w3 <<< 6),
    w3 >>> 25 ]

def maskedLow32 (w0 w1 w2 w3 : BitVec 64) (j : Fin 8) : BitVec 32 :=
  BitVec.extractLsb' 0 32
    ((sourceWords w0 w1 w2 w3)[j.val]'(by simp [sourceWords]) &&&
      (2147483647 : BitVec 64))

theorem source_word_masked_extract (w0 w1 w2 w3 : BitVec 64) (j : Fin 8) :
    maskedLow32 w0 w1 w2 w3 j =
      BitVec.zeroExtend 32
        ((packed256 w0 w1 w2 w3).extractLsb' (31 * j.val) 31) := by
  fin_cases j <;> simp only [maskedLow32, sourceWords, packed256] <;> bv_decide

#print axioms packed256
#print axioms sourceWords
#print axioms maskedLow32
#print axioms source_word_masked_extract

end AspisV8R19.R637PackedBitExtraction
