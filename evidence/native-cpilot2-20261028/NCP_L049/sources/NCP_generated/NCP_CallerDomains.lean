import NCP_DecodeReference
set_option autoImplicit false
namespace NCP_CallerDomains
open Aeneas Aeneas.Std

theorem range_length (bytes : List U8) (n start width : Nat)
    (length : bytes.length = n) (bound : start+width ≤ n) :
    ((bytes.drop start).take width).length = width := by
  simp only [List.length_take,List.length_drop,length]
  omega

theorem after_digest (bytes : List U8) (length : bytes.length = 688) (k : Fin 21) :
    ((bytes.drop (16+32*k.val)).take 32).length = 32 := by
  apply range_length bytes 688 _ 32 length
  have := k.isLt
  omega

theorem after_index (bytes : List U8) (length : bytes.length = 688) :
    ((bytes.drop 8).take 8).length = 8 :=
  range_length bytes 688 8 8 length (by decide)

#print axioms range_length
#print axioms after_digest
#print axioms after_index
end NCP_CallerDomains
