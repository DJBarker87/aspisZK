import AspisR1BatchedWeightsExtraction.Funs
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction
set_option autoImplicit false
namespace BWSetReadLemmasV4
abbrev Row := Array Std.U64 4#usize
abbrev Raw := alloc.vec.Vec Row
theorem set_read_ne (raw : Raw) (idx i : Usize) (row : Row) (hne : idx.val ≠ i.val) :
    Slice.index_usize (alloc.vec.Vec.set raw idx row : Slice Row) i = Slice.index_usize (raw : Slice Row) i := by
  simp [Slice.index_usize, alloc.vec.Vec.set, hne]
theorem set_read_eq (raw : Raw) (idx : Usize) (row : Row) (hbound : idx.val < raw.length) :
    Slice.index_usize (alloc.vec.Vec.set raw idx row : Slice Row) idx = .ok row := by
  simp [Slice.index_usize, alloc.vec.Vec.set, hbound]
#print axioms set_read_ne
#print axioms set_read_eq
end BWSetReadLemmasV4
