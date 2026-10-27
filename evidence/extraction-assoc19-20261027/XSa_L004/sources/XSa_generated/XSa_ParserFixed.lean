import XSa_ParserBytes
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSa_ParserFixed
open AspisR1.ExtractedRecordByteCanonicality

theorem fixed (b : Array U8 32#usize) :
 _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes (Array.to_slice b) =
 mapR (Option.map XSa_ParserBytes.toWide)
  (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice b)) := by
 rw [fixed_reads]
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes
 rw [XSa_ParserBytes.words]
 simp only [Array.to_slice,b.property]
 unfold wordArray8
 rw [AspisR1.ExtractedRecordLimbCanonicality.from_limbs_make]
 simp only [map_ok,Option.map_ite,Option.map_none,Option.map_some]
 rfl

#print axioms fixed
end XSa_ParserFixed
