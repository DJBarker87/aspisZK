import PCF_EncodePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_DigestFirst
open AspisR1.S2K

def words (a b c d e f g h : U32) : Array U32 8#usize :=
  Array.make 8#usize [a,b,c,d,e,f,g,h]

theorem first_words (a b c d e f g h : U32) :
    NFY_NBN_OutputLane.first (words a b c d e f g h) =
      (core.num.U32.to_le_bytes a).val[0]! := by
  unfold NFY_NBN_OutputLane.first DigestBytes.bytes
  have hv : (words a b c d e f g h).val = a::[b,c,d,e,f,g,h] := rfl
  rw [hv,PCF_EncodePrefix.head_zero]

#print axioms first_words
end PCF_DigestFirst
