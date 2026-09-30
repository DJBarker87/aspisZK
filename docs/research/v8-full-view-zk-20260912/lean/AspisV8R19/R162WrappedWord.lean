import Aeneas.Std
import Aeneas.Tactic.Conv.Bvify.Bvify

set_option autoImplicit false

namespace AspisV8R19.R162WrappedWord

open Aeneas.Std

def word (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩

theorem word_value (n : Nat) (h : n < 2^64) : (word n).val = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem word_value_mod (n : Nat) : (word n).val = n % 2^64 := by
  change (BitVec.ofNat 64 n).toNat = n % 2^64
  rw [BitVec.toNat_ofNat]

theorem wrapping_add_word (a b : Nat) :
    U64.wrapping_add (word a) (word b) = word (a + b) := by
  unfold U64.wrapping_add UScalar.wrapping_add word
  simp [BitVec.ofNat_add]

theorem wrapping_mul_word (a b : Nat) :
    U64.wrapping_mul (word a) (word b) = word (a * b) := by
  unfold U64.wrapping_mul UScalar.wrapping_mul word
  simp [BitVec.ofNat_mul]

theorem wrapping_sub_word (a b : Nat) (_hb : b < 2^64) (hle : b ≤ a) :
    U64.wrapping_sub (word a) (word b) = word (a - b) := by
  apply UScalar.eq_of_val_eq
  change (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat =
    (BitVec.ofNat 64 (a - b)).toNat
  exact congrArg BitVec.toNat
    (Aeneas.Bvify.BitVec.ofNat_sub' 64 a b hle).symm

theorem core_wrapping_add_word (a b : Nat) :
    core.num.U64.wrapping_add (word a) (word b) = word (a + b) :=
  wrapping_add_word a b

theorem core_wrapping_mul_word (a b : Nat) :
    core.num.U64.wrapping_mul (word a) (word b) = word (a * b) :=
  wrapping_mul_word a b

theorem core_wrapping_sub_word (a b : Nat) (_hb : b < 2^64) (hle : b ≤ a) :
    core.num.U64.wrapping_sub (word a) (word b) = word (a - b) :=
  wrapping_sub_word a b _hb hle

#print axioms word_value
#print axioms word_value_mod
#print axioms wrapping_add_word
#print axioms wrapping_mul_word
#print axioms wrapping_sub_word
#print axioms core_wrapping_add_word
#print axioms core_wrapping_mul_word
#print axioms core_wrapping_sub_word

end AspisV8R19.R162WrappedWord
