import R1Z.ProverCommitOwnedArrays
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result
open R0Z.FsStatement
open R1Z.ProverCommitStreamSource (Bytes32 blockSlices)

/-- Symbolic byte-count induction, independent of the counter value. -/
theorem littleEndian_bits (w : Nat) (bits : BitVec w) :
    littleEndian (bits.toLEBytes.map (@UScalar.mk .U8)) = bits.toNat := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    by_cases zero : w = 0
    · subst w
      have bound := bits.isLt
      simp only [pow_zero] at bound
      simp [BitVec.toLEBytes, littleEndian]
      omega
    · rw [BitVec.toLEBytes.eq_1]
      simp only [if_pos (by omega : w > 0), List.map_cons, littleEndian]
      rw [ih (w-8) (by omega)]
      change (bits.setWidth 8).toNat + 256 * ((bits >>> 8).setWidth (w-8)).toNat = bits.toNat
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      change bits.toNat % 256 + 256 * ((bits.toNat / 256) % 2^(w-8)) = bits.toNat
      have bound := bits.isLt
      by_cases wide : 8 ≤ w
      · have power : 2^w = 256 * 2^(w-8) := by
          calc
            2^w = 2^((w-8)+8) := by congr 1; omega
            _ = _ := by rw [Nat.pow_add]; ring
        rw [power] at bound
        have divbound : bits.toNat / 256 < 2^(w-8) := by omega
        rw [Nat.mod_eq_of_lt divbound]
        omega
      · have powbound : 2^w ≤ 256 := by
          exact Nat.pow_le_pow_right (by decide) (by omega : w ≤ 8)
        have small : bits.toNat < 256 := by omega
        rw [Nat.div_eq_of_lt small, Nat.zero_mod, Nat.mod_eq_of_lt small]
        omega

theorem littleEndian_counter (counter : U64) :
    littleEndian (core.num.U64.to_le_bytes counter).val = counter.val := by
  exact littleEndian_bits 64 counter.bv

def answerBytes (answer : OracleAnswer) : Bytes32 :=
  Aeneas.Std.Array.make 32#usize
    (List.ofFn (fun i : Fin 32 => UScalar.mk (BitVec.ofNat 8 ((answer i).toNat))))

/-- The backend supplies exactly block counter.val, including the last block.
No large finite input carrier is reduced or enumerated. -/
theorem blockHash_at {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (seed : Bytes32) (counter : U64) (bound : counter.val < n) :
    blockHash answers (blockSlices domain seed counter) =
      ok (answerBytes (answers ⟨counter.val, bound⟩)) := by
  simp only [blockHash, blockSlices, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, littleEndian_counter,
    dif_pos bound, answerBytes]
  rfl

theorem blockHash_end {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (seed : Bytes32) (counter : U64) (bound : n ≤ counter.val) :
    blockHash answers (blockSlices domain seed counter) = fail .panic := by
  simp only [blockHash, blockSlices, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, littleEndian_counter,
    dif_neg (not_lt.mpr bound)]

#print axioms littleEndian_bits
#print axioms littleEndian_counter
#print axioms blockHash_at
#print axioms blockHash_end
end R1Z.ProverCommitOwnedDecoder
