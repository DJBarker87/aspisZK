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
  rw [BitVec.getLsbD_setWidth' (by omega)]
  change (BitVec.fromLEBytes (b.val.map U8.bv)).toNat.testBit i = _
  rw [← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
  have hq : i / 8 < 31 := by omega
  simp [List.getElem!_map, hq, BitVec.getLsbD, Byte.testBit]

lemma bytePack_high (b : Array U8 31#usize) (i : Nat) (hi : 248 ≤ i) :
    (bytePack256 b).getLsbD i = false := by
  change ((chunkBits248 b).zeroExtend 256).getLsbD i = false
  rw [BitVec.getLsbD_setWidth' (by omega)]
  exact getLsbD_false_of_ge (chunkBits248 b) hi

/-- The four source-shaped little-endian reads reconstruct the 31-byte packing. -/
theorem packed_bytes_concat (b : Array U8 31#usize) :
    packed256 (word0 b) (word1 b) (word2 b) (word3 b) = bytePack256 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [packed_lsbD]
  sorry

#print axioms packed_bytes_concat
end AspisV8R19.R641PackedByteConcat
