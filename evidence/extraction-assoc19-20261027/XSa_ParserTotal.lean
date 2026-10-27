import XSa_ParserFixed
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSa_ParserTotal

theorem bytes (s : Slice U8) :
 _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s =
 mapR (Option.map XSa_ParserBytes.toWide)
  (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes s) := by
 by_cases hl : s.val.length=32
 · let b : Array U8 32#usize := ⟨s.val,hl⟩
   have hb : Array.to_slice b=s := by cases s; rfl
   simpa only [hb] using XSa_ParserFixed.fixed b
 · rw [AspisR1.ExtractedRecordByteCanonicality.wrong_length s hl,map_ok,Option.map_none]
   unfold _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes
   simp only [hl,false_and,if_false]

#print axioms bytes
end XSa_ParserTotal
