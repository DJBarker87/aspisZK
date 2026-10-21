import Aeneas
/- Exact emitted geometry layout/read declaration; no external backend. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace S7OwnedP6QueryRead
abbrev aspis_core.field.M31 := U32
structure QueryGeometry where
  start : Std.Usize
  inverses : alloc.vec.Vec (Array aspis_core.field.M31 5#usize)
  line_z : alloc.vec.Vec aspis_core.field.M31

def QueryGeometry.for_query
  (self : QueryGeometry) (index : Std.Usize) :
  Result (Array aspis_core.field.M31 5#usize)
  := do
  let i ← index - self.start
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array
    aspis_core.field.M31 5#usize)) self.inverses i


#print alloc.vec.Vec.index_usize_spec
#print alloc.vec.Vec.index
end S7OwnedP6QueryRead
