import XRt_QueryWord
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRt_QueryWords

def words (b : Array U8 32#usize) : List U32 :=
 (List.range 8).map fun j =>
 UScalar.ofNat ((XRn_Join_word ((b.val.drop (4*j)).take 4)).val % 262144)
  (by change _ ≤ 4294967295; omega)

theorem same_words (b : Array U8 32#usize) (out : Array U32 8#usize)
 (run : AspisR1QueryScanUnrolled.r0_transcript.query_words b = ok out) :
 words b = out.val := by
 rw [AspisR1QueryScanUnrolled.r0_transcript.query_words_success_byte_mask b out run]
 unfold words
 apply List.map_congr_left
 intro j hj
 have hj8 : j < 8 := List.mem_range.mp hj
 calc
  _ = AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
    (XRn_Join_word ((b.val.drop (4*j)).take 4)) := XRt_QueryWord.mask _
  _ = _ := congrArg AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
    (XRt_QueryWord.block_word b j hj8)

#print axioms same_words
end XRt_QueryWords
