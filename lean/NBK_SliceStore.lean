import NBH_Audit
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBK_SliceStore

def store (output : Slice U8) (start stop : Usize)
    (bytes : Array U8 32#usize) : Result (Slice U8) := do
  let (s, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8)
    output { start, «end» := stop }
  let src ← lift (Array.to_slice bytes)
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back copied)

theorem exact (output : Slice U8) (start stop : Usize)
    (bytes : Array U8 32#usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ output.length)
    (width : stop.val - start.val = 32) :
    store output start stop bytes = ok (output.setSlice! start.val bytes.val) := by
  have room : 32 ≤ output.length - start.val := by omega
  have bs := bytes.property
  simp only [store, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Array.to_slice]
  simp [Slice.length, Slice.len, order, bound, core.slice.Slice.copy_from_slice,
    List.slice, width, Nat.min_eq_left room, bs, Slice.setSlice!, lift]

#print axioms exact
end NBK_SliceStore
