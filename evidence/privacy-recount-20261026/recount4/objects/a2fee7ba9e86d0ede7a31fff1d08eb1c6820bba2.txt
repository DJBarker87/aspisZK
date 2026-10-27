import R1Z.ProverCommitSaltSource
import R1Z.LayoutR1PBin
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace R1Z.ProverCommitSaltBytes
open R1Z.ProverCommitSaltSource

def byte (x : U8) : UInt8 := x.val.toUInt8

theorem shift_byte (n : ℕ) (x : BitVec (n+8)) :
    ((x >>> 8).setWidth n).toNat = x.toNat / 256 := by
  have h : (x >>> 8).toNat < 2^n := by
    simpa using BitVec.toNat_ushiftRight_lt x 8 (by omega)
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem le32_source (index : U32) :
    (core.num.U32.to_le_bytes index).val.map byte = R1Z.TranscriptR1.le32 index.val := by
  let b0 := index.bv
  let b1 := (b0 >>> 8).setWidth 24
  let b2 := (b1 >>> 8).setWidth 16
  let b3 := (b2 >>> 8).setWidth 8
  unfold core.num.U32.to_le_bytes
  change (index.bv.toLEBytes.map (@UScalar.mk .U8)).map byte = _
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  change [((b0.setWidth 8).toNat).toUInt8,
    ((b1.setWidth 8).toNat).toUInt8,
    ((b2.setWidth 8).toNat).toUInt8,
    ((b3.setWidth 8).toNat).toUInt8] = _
  have h1 : b1.toNat = b0.toNat / 256 := shift_byte 24 b0
  have h2 : b2.toNat = b1.toNat / 256 := shift_byte 16 b1
  have h3 : b3.toNat = b2.toNat / 256 := shift_byte 8 b2
  rw [BitVec.toNat_setWidth 8 b0, BitVec.toNat_setWidth 8 b1,
    BitVec.toNat_setWidth 8 b2, BitVec.toNat_setWidth 8 b3]
  rw [h3, h2, h1]
  simp only [TranscriptR1.le32, UScalar.val, Nat.div_div_eq_div_mul]
  norm_num only
  rfl

theorem le64_source (counter : U64) :
    (core.num.U64.to_le_bytes counter).val.map byte = LayoutR1PBin.le64 counter.val := by
  let b0 := counter.bv
  let b1 := (b0 >>> 8).setWidth 56
  let b2 := (b1 >>> 8).setWidth 48
  let b3 := (b2 >>> 8).setWidth 40
  let b4 := (b3 >>> 8).setWidth 32
  let b5 := (b4 >>> 8).setWidth 24
  let b6 := (b5 >>> 8).setWidth 16
  let b7 := (b6 >>> 8).setWidth 8
  unfold core.num.U64.to_le_bytes
  change (counter.bv.toLEBytes.map (@UScalar.mk .U8)).map byte = _
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  change [((b0.setWidth 8).toNat).toUInt8,
    ((b1.setWidth 8).toNat).toUInt8,
    ((b2.setWidth 8).toNat).toUInt8,
    ((b3.setWidth 8).toNat).toUInt8,
    ((b4.setWidth 8).toNat).toUInt8,
    ((b5.setWidth 8).toNat).toUInt8,
    ((b6.setWidth 8).toNat).toUInt8,
    ((b7.setWidth 8).toNat).toUInt8] = _
  have h1 : b1.toNat = b0.toNat / 256 := shift_byte 56 b0
  have h2 : b2.toNat = b1.toNat / 256 := shift_byte 48 b1
  have h3 : b3.toNat = b2.toNat / 256 := shift_byte 40 b2
  have h4 : b4.toNat = b3.toNat / 256 := shift_byte 32 b3
  have h5 : b5.toNat = b4.toNat / 256 := shift_byte 24 b4
  have h6 : b6.toNat = b5.toNat / 256 := shift_byte 16 b5
  have h7 : b7.toNat = b6.toNat / 256 := shift_byte 8 b6
  rw [BitVec.toNat_setWidth 8 b0, BitVec.toNat_setWidth 8 b1, BitVec.toNat_setWidth 8 b2, BitVec.toNat_setWidth 8 b3, BitVec.toNat_setWidth 8 b4, BitVec.toNat_setWidth 8 b5, BitVec.toNat_setWidth 8 b6, BitVec.toNat_setWidth 8 b7]
  rw [h7, h6, h5, h4, h3, h2, h1]
  simp only [LayoutR1PBin.le64, UScalar.val, Nat.div_div_eq_div_mul]
  norm_num only
  rfl

def wireBytes (s : Slice (Slice U8)) : List UInt8 :=
  (s.val.flatMap (fun x => x.val)).map byte

theorem salt_bytes (binding nonce secret : Bytes32) (tag : U8) (index : U32) :
    wireBytes (saltSlices binding nonce secret tag index) =
      LayoutR1PBin.dLeafSalt ++ binding.val.map byte ++ nonce.val.map byte ++
        [byte tag] ++ TranscriptR1.le32 index.val ++ secret.val.map byte := by
  simp [wireBytes, saltSlices, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make,
    List.map_append, List.append_assoc,
    AspisR1ProverCommit.aspis_prover.state_only_entropy.LEAF_SALT_DOMAIN,
    le32_source, byte, LayoutR1PBin.dLeafSalt]

#print axioms shift_byte
#print axioms le32_source
#print axioms salt_bytes
#print axioms le64_source
end R1Z.ProverCommitSaltBytes
