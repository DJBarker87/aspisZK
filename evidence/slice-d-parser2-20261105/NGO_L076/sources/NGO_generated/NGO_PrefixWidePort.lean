import NGD_ParseReference
import UnrolledWideParserRefinement
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_PrefixWidePort
abbrev WireQ := AspisR1PrefixAggregateParser.field.QM31
abbrev CandQ := AspisR1CandidateParser.field.QM31
abbrev WireWide := AspisR1PrefixAggregateParser.field.wide_exact.WideExact
abbrev CandWide := AspisR1CandidateParser.field.wide_exact.WideExact
def toQ (q : WireQ) : CandQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toWide (q : WireWide) : CandWide := ⟨toQ q.c0,toQ q.c1⟩
/-- Complete rejection-preserving carrier map on all eight raw words. -/
theorem limbs (arr : Array U32 8#usize) :
    NGD_ParseReference.mapResult (Option.map toWide)
      (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs arr) =
      AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled arr := by
  unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
    AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled
  simp only [NGD_ParseReference.map_bind,NGD_ParseReference.map_if,
    NGD_ParseReference.map_ok,AspisR1PrefixAggregateParser.field.P,
    AspisR1CandidateParser.field.P,Option.map_none,Option.map_some,toWide,toQ]
/-- Both parsers read precisely the same original thirty-two bytes. No
canonicality or successful-parse premise is used. -/
theorem bytes (input : Slice U8) :
    NGD_ParseReference.mapResult (Option.map toWide)
      (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes input) =
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input := by
  unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes
    AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
  simp only [NGD_ParseReference.map_bind,NGD_ParseReference.map_if,
    NGD_ParseReference.map_ok,limbs,Option.map_none,
    AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN]
#print axioms limbs
#print axioms bytes
end NGO_PrefixWidePort
