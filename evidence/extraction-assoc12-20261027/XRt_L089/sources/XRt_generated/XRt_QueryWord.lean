import XRn_Join_QueryModel
import QueryScanConcreteWordsDecoder
import ExtractedRecordByteValue
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRt_QueryWord

theorem four (a b c d : U8) :
 XRn_Join_word [a,b,c,d] = core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d]) := by
 apply UScalar.eq_of_val_eq
 have hv := AspisR1.ExtractedRecordByteValue.from_le4_value a b c d
 change XRn_Join_Bytes.le32 [a,b,c,d] % 4294967296 = _
 simp only [XRn_Join_Bytes.le32,List.take_succ_cons,List.take_zero,List.foldr_cons,List.foldr_nil]
 have ha : a.val < 256 := by scalar_tac
 have hb : b.val < 256 := by scalar_tac
 have hc : c.val < 256 := by scalar_tac
 have hd : d.val < 256 := by scalar_tac
 omega

theorem slice_four (xs : List U8) (n : Nat) (h : n+4 ≤ xs.length) :
 (xs.drop n).take 4 = [xs[n],xs[n+1],xs[n+2],xs[n+3]] := by
 apply List.ext_getElem
 · simp only [List.length_take,List.length_drop,List.length_cons,List.length_nil]
   omega
 · intro i hi hj
   have hi4 : i < 4 := by simpa using hj
   interval_cases i <;> simp

theorem block_word (b : Array U8 32#usize) (j : Nat) (hj : j < 8) :
 XRn_Join_word ((b.val.drop (4*j)).take 4) =
 AspisR1QueryScanUnrolled.r0_transcript.blockRankWord b j := by
 have hlen : b.val.length = 32 := b.property
 rw [slice_four b.val (4*j) (by omega)]
 unfold AspisR1QueryScanUnrolled.r0_transcript.blockRankWord
 rw [dif_pos hj]
 exact four _ _ _ _

theorem mask (w : U32) :
 UScalar.ofNat (w.val % 262144) (by change _ ≤ 4294967295; omega) =
 AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord w := by
 apply UScalar.eq_of_val_eq
 change w.val % 262144 = w.val &&& 262143
 exact (Nat.and_two_pow_sub_one_eq_mod w.val 18).symm

#print axioms four
#print axioms slice_four
#print axioms block_word
#print axioms mask
end XRt_QueryWord
