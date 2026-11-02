import NEO_WindowFrame
import R1CandidateFieldParsers
set_option autoImplicit false
namespace NEO_PrefixSlices
open Aeneas Aeneas.Std Result

def headArray (bytes : Slice U8) (n : Usize) (bound : n.val ≤ bytes.val.length) : Array U8 n :=
 ⟨bytes.val.take n.val,by simp only [List.length_take];omega⟩

theorem range (bytes : Slice U8) (n start finish : Usize)
 (bound : n.val ≤ bytes.val.length) (order : start.val ≤ finish.val) (inside : finish.val ≤ n.val) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
  {start:=start,«end»:=finish} =
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  (headArray bytes n bound).to_slice {start:=start,«end»:=finish} := by
 have stop : finish.val ≤ bytes.val.length := by omega
 simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
  core.slice.index.SliceIndexRangeUsizeSlice.index,Slice.length,Array.to_slice,
  headArray,List.slice,order,inside,stop,List.drop_take,List.take_take]

/-- Complete CM31 parser Result is independent of every backing byte beyond
its two checked four-byte windows. No acceptance/canonicality is assumed. -/
theorem complex (bytes : Slice U8) (bound : 8 ≤ bytes.val.length) :
 AspisR1CandidateParser.field.CM31.from_le_bytes bytes =
 AspisR1CandidateParser.field.CM31.from_le_bytes (headArray bytes 8#usize bound).to_slice := by
 have first := range bytes 8#usize 0#usize 4#usize bound (by decide) (by decide)
 have second := range bytes 8#usize 4#usize 8#usize bound (by decide) (by decide)
 simp only [AspisR1CandidateParser.field.CM31.from_le_bytes,first,second]

#print axioms range
#print axioms complex
end NEO_PrefixSlices
