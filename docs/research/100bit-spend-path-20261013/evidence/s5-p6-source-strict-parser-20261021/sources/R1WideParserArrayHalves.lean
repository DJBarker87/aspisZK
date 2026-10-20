import R1CandidateParserByteOrder
import R1ParserArraySlice

/-! Fixed-width byte slices for the current 32-byte wide parser frame.
These are array/list plumbing facts and do not assert parser semantics. -/
set_option autoImplicit false

namespace AspisR1.WideParserArrayHalves

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec

def half0 (arr : Array U8 32#usize) : Array U8 16#usize :=
  AspisR1.ParserArraySlice.segment arr 0#usize 16#usize (by decide)

def half1 (arr : Array U8 32#usize) : Array U8 16#usize :=
  AspisR1.ParserArraySlice.segment arr 16#usize 16#usize (by decide)

def arrayBytes32 (arr : Array U8 32#usize) :
    Fin 32 → AspisR1.RetainedFieldByteCodec.Byte := fun i =>
  AspisV8R19.SqueezeOracleBridge.decodeByte
    (arr.val[i.val]'(by
      have hlen := arr.property
      change arr.val.length = 32 at hlen
      omega))

theorem slice_half0 (arr : Array U8 32#usize) :
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (Array.to_slice arr)
      { start := 0#usize, «end» := 16#usize } =
      Result.ok (Array.to_slice (half0 arr)) := by
  simpa [half0] using
    AspisR1.ParserArraySlice.slice_segment arr 0#usize 16#usize
      (by decide) 16#usize (by decide)

theorem slice_half1 (arr : Array U8 32#usize) :
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (Array.to_slice arr)
      { start := 16#usize, «end» := 32#usize } =
      Result.ok (Array.to_slice (half1 arr)) := by
  simpa [half1] using
    AspisR1.ParserArraySlice.slice_segment arr 16#usize 16#usize
      (by decide) 32#usize (by decide)

theorem half0_bytes (arr : Array U8 32#usize) :
    AspisR1.CandidateParserByteOrder.arrayBytes16 (half0 arr) =
      (fun i : Fin 16 => arrayBytes32 arr ⟨i.val, by omega⟩) := by
  funext i
  apply Fin.ext
  simp [AspisR1.CandidateParserByteOrder.arrayBytes16, arrayBytes32,
    half0, AspisR1.ParserArraySlice.segment]

theorem half1_bytes (arr : Array U8 32#usize) :
    AspisR1.CandidateParserByteOrder.arrayBytes16 (half1 arr) =
      (fun i : Fin 16 => arrayBytes32 arr ⟨16 + i.val, by omega⟩) := by
  funext i
  apply Fin.ext
  simp [AspisR1.CandidateParserByteOrder.arrayBytes16, arrayBytes32,
    half1, AspisR1.ParserArraySlice.segment]

#print axioms slice_half0
#print axioms slice_half1
#print axioms half0_bytes
#print axioms half1_bytes

end AspisR1.WideParserArrayHalves
