import NEO_QuadraticTotal
set_option autoImplicit false
namespace NEO_ParserFailures
open Aeneas Aeneas.Std Result
attribute [local irreducible] core.num.U32.from_le_bytes

theorem complex_short (bytes : Slice U8) (short : bytes.val.length<4) :
 ∃ error, AspisR1CandidateParser.field.CM31.from_le_bytes bytes=fail error := by
 have fit : ¬ (4#usize).val≤bytes.val.length := by change ¬4≤bytes.val.length; omega
 simp [AspisR1CandidateParser.field.CM31.from_le_bytes,core.slice.index.Slice.index,
  core.slice.index.SliceIndexRangeUsizeSlice.index,Slice.length,fit]

theorem quadratic_short (bytes : Slice U8) (short : bytes.val.length<8) :
 ∃ error, AspisR1CandidateParser.field.QM31.from_le_bytes bytes=fail error := by
 have fit : ¬ (8#usize).val≤bytes.val.length := by change ¬8≤bytes.val.length; omega
 simp [AspisR1CandidateParser.field.QM31.from_le_bytes,core.slice.index.Slice.index,
  core.slice.index.SliceIndexRangeUsizeSlice.index,Slice.length,fit]

theorem complex_bad_first (bytes : Slice U8) (a : Array U8 4#usize)
 (first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
 bytes {start:=0#usize,«end»:=4#usize}=ok a.to_slice)
 (bad : core.num.U32.from_le_bytes a>=AspisR1CandidateParser.field.P) :
 AspisR1CandidateParser.field.CM31.from_le_bytes bytes=ok none := by
 simp only [AspisR1CandidateParser.field.CM31.from_le_bytes,first,
  NEO_ByteCuts.conversion,NEO_ByteCuts.scalar,if_pos bad,bind_tc_ok,
  AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,NEO_ByteCuts.residual]

theorem quadratic_bad_first (bytes : Slice U8) (lo : Slice U8)
 (first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
 bytes {start:=0#usize,«end»:=8#usize}=ok lo)
 (bad : AspisR1CandidateParser.field.CM31.from_le_bytes lo=ok none) :
 AspisR1CandidateParser.field.QM31.from_le_bytes bytes=ok none := by
 simp only [AspisR1CandidateParser.field.QM31.from_le_bytes,first,bad,bind_tc_ok,
  AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,NEO_ByteCuts.residual]

#print axioms complex_short
#print axioms quadratic_short
#print axioms complex_bad_first
#print axioms quadratic_bad_first
end NEO_ParserFailures
