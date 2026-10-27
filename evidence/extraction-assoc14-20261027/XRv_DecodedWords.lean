import XRv_DecoderTotal
import XRt_QueryWords
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRv_DecodedWords

def decoded (b : Array U8 32#usize) : Array U32 8#usize :=
 ⟨XRt_QueryWords.words b, by simp only [XRt_QueryWords.words,List.length_map,List.length_range]; rfl⟩

theorem exact_result (b : Array U8 32#usize) :
 AspisR1QueryScanUnrolled.r0_transcript.query_words b = ok (decoded b) := by
 obtain ⟨out,hout⟩ := XRv_DecoderTotal.decoder b
 have hv := XRt_QueryWords.same_words b out hout
 have he : out = decoded b := Subtype.ext hv.symm
 exact hout.trans (congrArg Result.ok he)

theorem continuation {T : Type} (b : Array U8 32#usize) (k : Array U32 8#usize → Result T) :
 (AspisR1QueryScanUnrolled.r0_transcript.query_words b >>= k) = k (decoded b) := by
 rw [exact_result,bind_tc_ok]

theorem no_failure (b : Array U8 32#usize) (e : Error) :
 AspisR1QueryScanUnrolled.r0_transcript.query_words b ≠ fail e := by
 rw [exact_result]; intro h; cases h

theorem no_divergence (b : Array U8 32#usize) :
 AspisR1QueryScanUnrolled.r0_transcript.query_words b ≠ div := by
 rw [exact_result]; intro h; cases h

#print axioms exact_result
#print axioms continuation
#print axioms no_failure
#print axioms no_divergence
end XRv_DecodedWords
