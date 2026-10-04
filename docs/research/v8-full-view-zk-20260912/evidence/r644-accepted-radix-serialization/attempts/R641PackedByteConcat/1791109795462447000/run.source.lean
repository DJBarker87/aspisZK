import AspisV8R19.R637PackedBitExtraction
import AspisV8R19.R639PackedByteBits

set_option autoImplicit false

namespace AspisV8R19.R641PackedByteConcat

open Aeneas Aeneas.Std
open AspisV8R19.R623PackedDecoderExecution
open AspisV8R19.R637PackedBitExtraction
open AspisV8R19.R639PackedByteBits

def chunkBits248 (b : Array U8 31#usize) : BitVec 248 :=
  (BitVec.fromLEBytes (b.val.map U8.bv)).cast (by simp [b.property])

def bytePack256 (b : Array U8 31#usize) : BitVec 256 :=
  (chunkBits248 b).zeroExtend 256

def word0 (b : Array U8 31#usize) : BitVec 64 :=
  (core.num.U64.from_le_bytes (eight b 0 (by omega))).bv

def word1 (b : Array U8 31#usize) : BitVec 64 :=
  (core.num.U64.from_le_bytes (eight b 8 (by omega))).bv

def word2 (b : Array U8 31#usize) : BitVec 64 :=
  (core.num.U64.from_le_bytes (eight b 16 (by omega))).bv

def word3 (b : Array U8 31#usize) : BitVec 64 :=
  (Std.U64.wrapping_shr (core.num.U64.from_le_bytes (eight b 23 (by omega))) 8#u32).bv

lemma bytePack_low (b : Array U8 31#usize) (i : Nat) (hi : i < 248) :
    (bytePack256 b).getLsbD i =
      (b.val[i / 8]'(by have hb : b.val.length = 31 := b.property; omega)).bv.getLsbD (i % 8) := by
  change ((chunkBits248 b).zeroExtend 256).getLsbD i = _
  rw [BitVec.zeroExtend_eq_setWidth]
  unfold BitVec.setWidth
  split
  · rw [BitVec.getLsbD_setWidth']
    change (BitVec.fromLEBytes (b.val.map U8.bv)).toNat.testBit i = _
    rw [← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
    have hq : i / 8 < 31 := by omega
    simp [hq, BitVec.getLsbD, Byte.testBit]
  · omega

lemma bytePack_high (b : Array U8 31#usize) (i : Nat) (hi : 248 ≤ i) :
    (bytePack256 b).getLsbD i = false := by
  change ((chunkBits248 b).zeroExtend 256).getLsbD i = false
  rw [BitVec.zeroExtend_eq_setWidth]
  unfold BitVec.setWidth
  split
  · rw [BitVec.getLsbD_setWidth']
    exact getLsbD_false_of_ge (chunkBits248 b) hi
  · omega

/-- The four source-shaped little-endian reads reconstruct the 31-byte packing. -/
theorem packed_bytes_concat (b : Array U8 31#usize) :
    packed256 (word0 b) (word1 b) (word2 b) (word3 b) = bytePack256 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [packed_lsbD]
  by_cases h0 : i < 64
  · rw [if_pos h0, bytePack_low b i (by omega)]
    simpa [word0] using eight_from_le_bytes_bit b 0 (by omega) i h0
  · rw [if_neg h0]
    by_cases h1 : i < 128
    · rw [if_pos h1, bytePack_low b i (by omega)]
      have hj : i - 64 < 64 := by omega
      have hdiv : 8 + (i - 64) / 8 = i / 8 := by omega
      have hmod : (i - 64) % 8 = i % 8 := by omega
      simpa [word1, hdiv, hmod] using
        eight_from_le_bytes_bit b 8 (by omega) (i - 64) hj
    · rw [if_neg h1]
      by_cases h2 : i < 192
      · rw [if_pos h2, bytePack_low b i (by omega)]
        have hj : i - 128 < 64 := by omega
        have hdiv : 16 + (i - 128) / 8 = i / 8 := by omega
        have hmod : (i - 128) % 8 = i % 8 := by omega
        simpa [word2, hdiv, hmod] using
          eight_from_le_bytes_bit b 16 (by omega) (i - 128) hj
      · rw [if_neg h2]
        by_cases h248 : i < 248
        · rw [bytePack_low b i (by omega)]
          have hj : i - 192 < 56 := by omega
          have hbit : i - 192 + 8 < 64 := by omega
          have hdiv : 23 + (i - 192 + 8) / 8 = i / 8 := by omega
          have hmod : (i - 192 + 8) % 8 = i % 8 := by omega
          simpa [word3, U64.wrapping_shr_bv_eq, BitVec.getLsbD_ushiftRight,
            hdiv, hmod] using
            eight_from_le_bytes_bit b 23 (by omega) (i - 192 + 8) hbit
        · rw [bytePack_high b i (by omega)]
          unfold word3
          rw [U64.wrapping_shr_bv_eq]
          have hs : (8#u32).val % 64 = 8 := by scalar_tac
          rw [hs, BitVec.getLsbD_ushiftRight]
          exact getLsbD_false_of_ge
            (core.num.U64.from_le_bytes (eight b 23 (by omega))).bv (by omega)

#print axioms packed_bytes_concat
end AspisV8R19.R641PackedByteConcat
