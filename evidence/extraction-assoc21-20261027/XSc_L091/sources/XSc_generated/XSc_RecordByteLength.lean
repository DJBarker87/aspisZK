import XSc_RecordFieldStep
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_RecordByteLength
abbrev Old := AspisR1PrefixAggregateParser.field.wide_exact.WideExact
def mapped (bytes : Slice U8) : Result (Option XRn_Join_Wide) :=
 XRo_Join_Carriers.mapR (fun x : Option Old => x.map XSc_RecordFieldTypes.wide)
  (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes)
/-- Preserve both decoders' length rejection before selecting any byte. -/
theorem source (bytes : Slice U8) (length : bytes.val.length≠32) :
 mapped bytes=_root_.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes := by
 unfold mapped AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes
 have different : Slice.len bytes≠AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN := by
  intro eq
  apply length
  have values := congrArg UScalar.val eq
  simpa only [AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN] using values
 have wrong : Slice.len bytes != AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN := by
  simpa only [bne_iff_ne] using different
 rw [if_pos wrong]
 simp only [XRo_Join_Carriers.mapR,bind_tc_ok,Option.map_none]
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes
 simp only [length,false_and,if_false]
#print axioms source
end XSc_RecordByteLength
