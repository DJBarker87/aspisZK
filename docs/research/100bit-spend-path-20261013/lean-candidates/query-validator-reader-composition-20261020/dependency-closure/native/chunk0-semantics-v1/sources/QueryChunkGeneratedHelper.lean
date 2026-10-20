import Aeneas
import QueryChunkPrefixSemantics
open Aeneas Aeneas.Std Result

namespace AspisR1.QueryValidatorGeneratedChunk

def duplicateChunk0
    (queries : Array Std.U32 22#usize) (needle : Std.U32) (count : Std.Usize) : Result Bool := do
  let i ← Array.index_usize queries 0#usize
  let i1 ← Array.index_usize queries 1#usize
  let i2 ← Array.index_usize queries 2#usize
  let i3 ← Array.index_usize queries 3#usize
  let i4 ← Array.index_usize queries 4#usize
  let i5 ← Array.index_usize queries 5#usize
  let i6 ← Array.index_usize queries 6#usize
  let i7 ← Array.index_usize queries 7#usize
  ok (((((((((count > 0#usize) && (i = needle)) || ((count > 1#usize) && (i1 = needle))) ||
    ((count > 2#usize) && (i2 = needle))) || ((count > 3#usize) && (i3 = needle))) ||
    ((count > 4#usize) && (i4 = needle))) || ((count > 5#usize) && (i5 = needle))) ||
    ((count > 6#usize) && (i6 = needle))) || ((count > 7#usize) && (i7 = needle)))

theorem duplicateChunk0_eq_formula
    (queries : Array Std.U32 22#usize) (needle : Std.U32) (count : Std.Usize)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Std.U32)
    (h0 : Array.index_usize queries 0#usize = ok x0)
    (h1 : Array.index_usize queries 1#usize = ok x1)
    (h2 : Array.index_usize queries 2#usize = ok x2)
    (h3 : Array.index_usize queries 3#usize = ok x3)
    (h4 : Array.index_usize queries 4#usize = ok x4)
    (h5 : Array.index_usize queries 5#usize = ok x5)
    (h6 : Array.index_usize queries 6#usize = ok x6)
    (h7 : Array.index_usize queries 7#usize = ok x7) :
    duplicateChunk0 queries needle count = ok
      (((((((((count > 0#usize) && (x0 = needle)) || ((count > 1#usize) && (x1 = needle))) ||
       ((count > 2#usize) && (x2 = needle))) || ((count > 3#usize) && (x3 = needle))) ||
       ((count > 4#usize) && (x4 = needle))) || ((count > 5#usize) && (x5 = needle))) ||
       ((count > 6#usize) && (x6 = needle))) || ((count > 7#usize) && (x7 = needle))) := by
  simp only [duplicateChunk0, h0, h1, h2, h3, h4, h5, h6, h7, bind_tc_ok]

def formula0 (count : Std.Usize) (x0 x1 x2 x3 x4 x5 x6 x7 needle : Std.U32) : Bool :=
  (((((((((count > 0#usize) && (x0 = needle)) || ((count > 1#usize) && (x1 = needle))) ||
    ((count > 2#usize) && (x2 = needle))) || ((count > 3#usize) && (x3 = needle))) ||
    ((count > 4#usize) && (x4 = needle))) || ((count > 5#usize) && (x5 = needle))) ||
    ((count > 6#usize) && (x6 = needle))) || ((count > 7#usize) && (x7 = needle)))

theorem formula0_true_iff (count : Std.Usize) (x0 x1 x2 x3 x4 x5 x6 x7 needle : Std.U32) :
    formula0 count x0 x1 x2 x3 x4 x5 x6 x7 needle = true ↔
      (((count > 0#usize) = true ∧ (x0 = needle) = true) ∨
       ((count > 1#usize) = true ∧ (x1 = needle) = true) ∨
       ((count > 2#usize) = true ∧ (x2 = needle) = true) ∨
       ((count > 3#usize) = true ∧ (x3 = needle) = true) ∨
       ((count > 4#usize) = true ∧ (x4 = needle) = true) ∨
       ((count > 5#usize) = true ∧ (x5 = needle) = true) ∨
       ((count > 6#usize) = true ∧ (x6 = needle) = true) ∨
       ((count > 7#usize) = true ∧ (x7 = needle) = true)) := by
  simp [formula0, or_assoc]

end AspisR1.QueryValidatorGeneratedChunk
