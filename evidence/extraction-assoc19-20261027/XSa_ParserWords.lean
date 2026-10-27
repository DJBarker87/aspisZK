import XRy_ClaimSelectExtra
import XRt_QueryWord
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_ParserWords

/-- The two byte decoders call the SAME primitive on each four-byte cell. -/
theorem word (b : Array U8 32#usize) (j : Fin 8) :
 XRn_Join_word ((b.val.drop (4*j.val)).take 4) =
 AspisR1.ExtractedRecordByteCanonicality.wordLE b j := by
 have hl : b.val.length=32 := b.property
 rw [XRt_QueryWord.slice_four b.val (4*j.val) (by omega)]
 unfold AspisR1.ExtractedRecordByteCanonicality.wordLE
   AspisR1.ExtractedRecordByteCanonicality.byteAt
 exact XRt_QueryWord.four _ _ _ _

#print axioms word
end XSa_ParserWords
