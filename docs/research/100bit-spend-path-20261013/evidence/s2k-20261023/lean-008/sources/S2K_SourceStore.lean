import S2G_InstalledValues
import S2K_FrontierCases

/-! The exact Array.index_mut / slice copy / index_mut_back sequence used
by the afterstate encoder. Symbolic buffers only; no native certificate is
converted into a Lean premise. The iterator and digest call remain separate. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.SourceStore

def store (output : Array U8 688#usize) (start stop : Usize)
    (bytes : Array U8 32#usize) : Result (Array U8 688#usize) := do
  let (s, back) ← core.array.Array.index_mut
    (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    output { start, «end» := stop }
  let src ← lift (Array.to_slice bytes)
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back copied)

theorem store_exact (output : Array U8 688#usize) (start stop : Usize)
    (bytes : Array U8 32#usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ 688)
    (width : stop.val - start.val = 32) :
    store output start stop bytes = ok (output.setSlice! start.val bytes.val) := by
  have room : 32 ≤ 688 - start.val := by omega
  have size := output.property
  have bs := bytes.property
  simp only [store, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Array.to_slice]
  simp [Slice.length, Slice.len, order, bound, size, core.slice.Slice.copy_from_slice,
    List.slice, width, Nat.min_eq_left room, bs, Array.from_slice, Array.setSlice!, lift]
  rfl

#print axioms store_exact
end AspisR1.S2K.SourceStore
