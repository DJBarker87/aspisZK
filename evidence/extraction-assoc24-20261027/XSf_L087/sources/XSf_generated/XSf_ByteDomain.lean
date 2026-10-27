import XSf_A3Ports
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSf_ByteDomain
open AspisR1

theorem word_at (b : Array U8 32#usize) (j : Nat) (hj : j<8) :
 LPq_BytesTotal.word (Array.to_slice b) j =
 AspisR1.ExtractedRecordByteCanonicality.wordLE b ⟨j,hj⟩ := by
 have len : b.val.length=32 := b.property
 unfold LPq_BytesTotal.word LPq_BytesTotal.byte
   AspisR1.ExtractedRecordByteCanonicality.wordLE AspisR1.ExtractedRecordByteCanonicality.byteAt
 simp only [Array.to_slice,List.getElem?_eq_getElem (show 4*j<b.val.length by omega),
   List.getElem?_eq_getElem (show 4*j+1<b.val.length by omega),
   List.getElem?_eq_getElem (show 4*j+2<b.val.length by omega),
   List.getElem?_eq_getElem (show 4*j+3<b.val.length by omega),Option.getD_some]

theorem decoded (s : Slice U8) (x : C.E)
 (run : _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s=ok (some x)) :
 s.val.length=32 ∧ ∀ j : Nat, j<8 → (LPq_BytesTotal.word s j).val<2147483647 := by
 rw [XSa_ParserTotal.bytes] at run
 cases hr : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes s with
 | fail e => simp only [hr,mapR,bind_tc_fail] at run; cases run
 | div => simp only [hr,mapR,bind_tc_div] at run; cases run
 | ok opt =>
   cases opt with
   | none => simp only [hr,mapR,bind_tc_ok,Option.map_none] at run; cases run
   | some w =>
     obtain ⟨len,b,hb,hwords,_⟩ := AspisR1.ExtractedRecordByteCanonicality.slice_success s w hr
     refine ⟨len,?_⟩
     intro j hj
     rw [←hb,word_at b j hj]
     exact hwords ⟨j,hj⟩

/-- ByteDomain follows from the actual selected parser calls. Canonical word
bounds are conclusions, not added observations or an assumed decoded value. -/
theorem from_decoders (y1 : Slice U8)
 (calls : ∀ l : Usize, l.val<29 → ∃ b : Slice U8, ∃ x : C.E,
   LPq_SelectedDomain.selected y1 l=ok b ∧
   _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes b=ok (some x)) :
 LPq_SelectedDomain.ByteDomain y1 := by
 intro l hl
 obtain ⟨b,x,selected,parsed⟩ := calls l hl
 obtain ⟨len,words⟩ := decoded b x parsed
 exact ⟨b,selected,len,words⟩

#print axioms word_at
#print axioms decoded
#print axioms from_decoders
end XSf_ByteDomain
