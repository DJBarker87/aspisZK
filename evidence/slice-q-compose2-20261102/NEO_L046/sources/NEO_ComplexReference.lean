import NEO_WindowV2.Funs
import NEO_PrefixSlices
set_option autoImplicit false
namespace NEO_ComplexReference
open Aeneas Aeneas.Std Result

def observe (c : AspisR1CandidateParser.field.CM31) : Array U32 2#usize :=
 Array.make 2#usize [c.a,c.b]

/-- Full Result on an arbitrary eight-byte window, with both scalar rejection
positions retained. No accepted encoding premise is used. -/
theorem eight (a b c d e f g h : U8) :
 NEO_WindowV2.complex (Array.make 8#usize [a,b,c,d,e,f,g,h]).to_slice =
 (do let parsed ← AspisR1CandidateParser.field.CM31.from_le_bytes
       (Array.make 8#usize [a,b,c,d,e,f,g,h]).to_slice
     ok (parsed.map observe)) := by
 simp [NEO_WindowV2.complex,NEO_WindowV2.word,NEO_WindowV2.P,
  AspisR1CandidateParser.field.CM31.from_le_bytes,AspisR1CandidateParser.field.M31.from_le_bytes,
  AspisR1CandidateParser.field.P,AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
  AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
  core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
  core.slice.index.SliceIndexRangeUsizeSlice.index,core.array.TryFromArrayCopySlice.try_from,
  Array.to_slice,Array.make,Slice.index_usize,Slice.len,Slice.length,List.slice,
  observe,lift,bind_tc_ok]
 repeat' split
 all_goals simp_all

#print axioms eight
end NEO_ComplexReference
