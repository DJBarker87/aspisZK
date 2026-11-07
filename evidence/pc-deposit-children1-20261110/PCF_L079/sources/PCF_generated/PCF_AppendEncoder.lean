import PCF_DigestFirst
import PCB_AppendFullRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_AppendEncoder
/-- Fixed eight symbolic words, four bytes each: no recurrence or concrete field reduction. -/
theorem words (a b c d e f g h : U32) :
    PCB_AppendFullRef.encode_digest_canonical (PCF_DigestFirst.words a b c d e f g h) =
      ok (AspisR1.S2K.DigestBytes.bytes (PCF_DigestFirst.words a b c d e f g h)) := by
  rfl
#print axioms words
end PCF_AppendEncoder
