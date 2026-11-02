import NEO_PrefixSlices
set_option autoImplicit false
namespace NEO_ByteCuts
open Aeneas Aeneas.Std Result
attribute [local irreducible] core.num.U32.from_le_bytes

theorem conversion (a : Array U8 4#usize) :
 core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 a.to_slice=ok (.Ok a) := by
 simp [core.array.TryFromArrayCopySlice.try_from,Array.to_slice,Slice.length,a.property]

theorem scalar (a : Array U8 4#usize) :
 AspisR1CandidateParser.field.M31.from_le_bytes a=
 ok (if core.num.U32.from_le_bytes a >= AspisR1CandidateParser.field.P
     then none else some (core.num.U32.from_le_bytes a)) := by
 simp only [AspisR1CandidateParser.field.M31.from_le_bytes,lift,bind_tc_ok]
 split <;> rfl

theorem residual (T : Type) :
 AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  T none=ok none := by
 simp [AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
  massert,read_discriminant,AspisR1CandidateParser.optionDiscriminant,
  AspisR1CandidateParser.optionTag,bind_tc_ok]

/-- Symbolic two-word plumbing. Byte-order operations remain opaque, so no
large generated bitvector expression is normalized while composing the parser. -/
theorem complex (bytes : Slice U8) (a b : Array U8 4#usize)
 (first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  bytes {start:=0#usize,«end»:=4#usize}=ok a.to_slice)
 (second : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  bytes {start:=4#usize,«end»:=8#usize}=ok b.to_slice) :
 AspisR1CandidateParser.field.CM31.from_le_bytes bytes =
 ok (if core.num.U32.from_le_bytes a >= AspisR1CandidateParser.field.P then none
     else if core.num.U32.from_le_bytes b >= AspisR1CandidateParser.field.P then none
     else some ({a:=core.num.U32.from_le_bytes a,b:=core.num.U32.from_le_bytes b} :
      AspisR1CandidateParser.field.CM31)) := by
 by_cases ha : core.num.U32.from_le_bytes a >= AspisR1CandidateParser.field.P
 · simp only [AspisR1CandidateParser.field.CM31.from_le_bytes,first,conversion,
    scalar,if_pos ha,bind_tc_ok,AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,residual]
 · by_cases hb : core.num.U32.from_le_bytes b >= AspisR1CandidateParser.field.P
   · simp only [AspisR1CandidateParser.field.CM31.from_le_bytes,first,second,conversion,
      scalar,if_neg ha,if_pos hb,bind_tc_ok,AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,residual]
   · simp only [AspisR1CandidateParser.field.CM31.from_le_bytes,first,second,conversion,
      scalar,if_neg ha,if_neg hb,bind_tc_ok,AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch]

#print axioms conversion
#print axioms scalar
#print axioms residual
#print axioms complex
end NEO_ByteCuts
