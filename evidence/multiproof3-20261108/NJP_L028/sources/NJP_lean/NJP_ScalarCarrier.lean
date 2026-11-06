import NJP_DigestCarrier

set_option autoImplicit false
namespace NJP_ScalarCarrier
open Aeneas Aeneas.Std Result

def word (n : Nat) : U32 := ⟨BitVec.ofNat 32 n⟩
def size (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩

theorem word_value (n : Nat) (bound : n < 2^32) : (word n).val=n := by
 change n % 2^32=n
 exact Nat.mod_eq_of_lt bound

theorem word_roundtrip (x : U32) : word x.val=x := by
 apply UScalar.eq_of_val_eq
 exact word_value x.val x.bv.isLt

theorem size_value (n : Nat) (bound : n < 2^64) : (size n).val=n := by
 change n % 2^64=n
 exact Nat.mod_eq_of_lt bound

theorem size_roundtrip (x : Usize) : size x.val=x := by
 apply UScalar.eq_of_val_eq
 exact size_value x.val x.bv.isLt

theorem half (x : U32) : (x.bv >>> 1).toNat=x.val/2 := by
 simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.pow_one]

theorem parity (x : U32) : (x.bv &&& (1 : BitVec 32)).toNat=x.val%2 := by
 simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
 exact Nat.and_one_is_mod _

theorem sibling (x : U32) : (x.bv ^^^ (1 : BitVec 32)).toNat=Nat.xor x.val 1 := by
 simp only [BitVec.toNat_xor,BitVec.toNat_ofNat]
 rfl

#print word_value
#print axioms word_value
#print word_roundtrip
#print axioms word_roundtrip
#print size_value
#print axioms size_value
#print size_roundtrip
#print axioms size_roundtrip
#print half
#print axioms half
#print parity
#print axioms parity
#print sibling
#print axioms sibling
end NJP_ScalarCarrier
