import NMX_ScalarCarrier
set_option autoImplicit false
namespace NMX_InverseScalars
open Aeneas Aeneas.Std NMX_Carrier NMX_ScalarCarrier

def fromWord (w : UInt32) : U32 := UScalar.ofNatCore w.toNat (UInt32.toNat_lt w)
def fromLong (w : UInt64) : U64 := UScalar.ofNatCore w.toNat (UInt64.toNat_lt w)

theorem word_roundtrip (w : U32) : fromWord (word w) = w := by
 apply UScalar.eq_of_val_eq
 simp only [fromWord,UScalar.ofNatCore_val_eq,word_value]

theorem long_roundtrip (w : U64) : fromLong (long w) = w := by
 apply UScalar.eq_of_val_eq
 simp only [fromLong,UScalar.ofNatCore_val_eq,long_value]

theorem native_word_roundtrip (w : UInt32) : word (fromWord w) = w := by
 simp [fromWord,word,UScalar.ofNatCore_val_eq]

theorem native_long_roundtrip (w : UInt64) : long (fromLong w) = w := by
 simp [fromLong,long,UScalar.ofNatCore_val_eq]
#print axioms word_roundtrip
#print axioms long_roundtrip
#print axioms native_word_roundtrip
#print axioms native_long_roundtrip
end NMX_InverseScalars
