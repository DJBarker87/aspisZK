import R1Z.ProverCommitOwnedBytes
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std
open R0Z.FsStatement R1Z.FinalR1PBin
open R1Z.ProverCommitStreamSource (Bytes32)

theorem fromLEBytes_value (bytes : List U8) :
    (BitVec.fromLEBytes (bytes.map U8.bv)).toNat = littleEndian bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have bound := (BitVec.fromLEBytes (bs.map U8.bv)).isLt
    simp only [List.length_map] at bound
    have bytebound : b.bv.toNat < 2^8 := b.bv.isLt
    have bytebound' : b.bv.toNat < 256 := by norm_num at bytebound ⊢; exact bytebound
    have power : 2^(8*(bs.length+1)) = 256*2^(8*bs.length) := by
      rw [Nat.mul_add, Nat.pow_add]
      ring
    have pos : 0 < 2^(8*bs.length) := by positivity
    have bsmall : b.bv.toNat < 2^(8*(bs.length+1)) := by rw [power]; omega
    have tsmall : (BitVec.fromLEBytes (bs.map U8.bv)).toNat < 2^(8*(bs.length+1)) := by rw [power]; omega
    have shiftSmall : (BitVec.fromLEBytes (bs.map U8.bv)).toNat * 2^8 < 2^(8*(bs.length+1)) := by rw [power]; norm_num; omega
    simp only [List.map_cons, BitVec.fromLEBytes.eq_2, BitVec.toNat_or,
      BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, List.length_map,
      List.length_cons, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt bsmall, Nat.mod_eq_of_lt tsmall, Nat.mod_eq_of_lt shiftSmall]
    rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt bytebound]
    simp only [Nat.shiftLeft_eq, ih, littleEndian]
    change littleEndian bs * 2^8 + b.val = b.val + 256 * littleEndian bs
    norm_num
    omega

/-- The finite equivalence's digit convention is the same four-byte load. -/
theorem blockW_value (answer : OracleAnswer) (j : Fin 8) :
    (blockW answer j).val =
      (answer ⟨4*j.val, by omega⟩).toNat +
      256*(answer ⟨4*j.val+1, by omega⟩).toNat +
      65536*(answer ⟨4*j.val+2, by omega⟩).toNat +
      16777216*(answer ⟨4*j.val+3, by omega⟩).toNat := by
  simp only [blockW, Equiv.trans_apply, Equiv.arrowCongr_apply,
    Equiv.refl_apply, Equiv.curry_apply, finFunctionFinEquiv_apply,
    finCongr_apply]
  simp [Fin.sum_univ_succ, R1Z.LensR1.uint8Equiv, finProdFinEquiv]
  <;> ring

theorem byteWord_answer (answer : OracleAnswer) (j : Fin 8) :
    wordFin (byteWord (answerBytes answer) j) = blockW answer j := by
  apply Fin.ext
  rw [blockW_value]
  change (core.num.U32.from_le_bytes _).val = _
  simp only [core.num.U32.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  rw [fromLEBytes_value]
  simp only [byteAt, answerBytes, Aeneas.Std.Array.make, List.getElem_ofFn,
    littleEndian, UScalar.val]
  simp only [UScalar.mk, UScalar.bv, UScalarTy.U8_numBits_eq, BitVec.toNat_ofNat]
  have small (i : Fin 32) : (answer i).toNat < 2^8 := (answer i).toFin.isLt
  simp only [Nat.mod_eq_of_lt (small _)]
  omega

#print axioms fromLEBytes_value
#print axioms blockW_value
#print axioms byteWord_answer
end R1Z.ProverCommitOwnedDecoder
