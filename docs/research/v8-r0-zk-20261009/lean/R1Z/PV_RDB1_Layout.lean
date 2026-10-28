import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_Layout

/-- Rust's actual pad_to_align mask, for a power-of-two alignment. This
identity is modular at arbitrary machine width; it never enumerates words. -/
theorem padded_mask (wordBits alignBits k : Nat) :
    (BitVec.ofNat wordBits (2^alignBits*k) +
      BitVec.ofNat wordBits (2^alignBits-1)) &&&
      ~~~(BitVec.ofNat wordBits (2^alignBits-1)) =
      BitVec.ofNat wordBits (2^alignBits*k) := by
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hm : 2^alignBits-1 < 2^alignBits := by
    have hp := Nat.two_pow_pos alignBits
    omega
  have hz : 0 < 2^alignBits := Nat.two_pow_pos _
  have hsum := Nat.testBit_two_pow_mul_add k hm i
  have hbase := Nat.testBit_two_pow_mul_add k hz i
  simp only [Nat.add_zero] at hbase
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
    hsum, hbase, Nat.testBit_two_pow_sub_one]
  by_cases hw : i < wordBits <;> by_cases ha : i < alignBits <;>
    simp [hw,ha]

structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq

def pad (wordBits : Nat) (layout : Layout) : Layout :=
  ⟨((BitVec.ofNat wordBits layout.size + BitVec.ofNat wordBits (layout.align-1))
    &&& ~~~(BitVec.ofNat wordBits (layout.align-1))).toNat,layout.align⟩

theorem pad_element (wordBits alignBits k : Nat)
    (representable : 2^alignBits*k < 2^wordBits) :
    pad wordBits ⟨2^alignBits*k,2^alignBits⟩ = ⟨2^alignBits*k,2^alignBits⟩ := by
  simp only [pad,padded_mask,BitVec.toNat_ofNat,Nat.mod_eq_of_lt representable]

/-- The shared repeat_packed computation keeps both checked multiplication
and the alignment-dependent size limit. -/
def packed (wordMax byteMax : Nat) (layout : Layout) (n : Nat) : Except Unit Layout :=
  if layout.size*n > wordMax then .error () else
  if layout.size*n > byteMax+1-layout.align then .error () else
  .ok ⟨layout.size*n,layout.align⟩

/-- Deployed repeat first pads, then calls repeat_packed, then maps away the
stride. For a Rust element layout the preceding mask theorem proves pad is
identity. Preserve every error and the exact returned layout. -/
theorem repeat_complete (wordMax byteMax n : Nat) (layout padded : Layout)
    (pad_identity : padded = layout) :
    (match packed wordMax byteMax padded n with
      | .error e => Except.error e
      | .ok repeated => Except.ok (repeated,padded.size)).map Prod.fst =
      packed wordMax byteMax layout n := by
  subst padded
  cases packed wordMax byteMax layout n <;> rfl

theorem constructor_guard (size maxSize : Nat) :
    (if size > maxSize then Except.error () else Except.ok size) =
      (if size ≤ maxSize then Except.ok size else Except.error ()) := by
  by_cases h : size ≤ maxSize
  · simp only [h,not_lt.mpr h,ite_false,ite_true]
  · have hh : maxSize < size := by omega
    simp only [h,hh,ite_true,ite_false]

#print axioms pad_element
#print axioms padded_mask
#print axioms repeat_complete
#print axioms constructor_guard
end R1Z.PV_RDB1_Layout
