import Aeneas
set_option autoImplicit false
noncomputable section
namespace NBP_Store
open Aeneas Aeneas.Std Result

def store {N W : Usize} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) : Result (Array U8 N) := do
  let (s,back) ← core.array.Array.index_mut
    (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    output {start,«end»:=stop}
  let src ← lift (Array.to_slice bytes)
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back copied)

theorem exact {N W : Usize} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    store output start stop bytes = ok (output.setSlice! start.val bytes.val) := by
  have room : W.val ≤ N.val-start.val := by omega
  simp only [store,core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,Array.to_slice]
  simp [Slice.length,Slice.len,order,bound,output.property,bytes.property,
    core.slice.Slice.copy_from_slice,List.slice,width,Nat.min_eq_left room,
    Array.from_slice,lift]
  rfl

theorem store_then {N W : Usize} {T : Type} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) (k : Array U8 N → Result T)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    (do
      let (s,back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        output {start,«end»:=stop}
      let src ← lift (Array.to_slice bytes)
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
      k (back copied)) = k (output.setSlice! start.val bytes.val) := by
  have h := congrArg (fun r => r >>= k) (exact output start stop bytes order bound width)
  cases indexed : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      output {start,«end»:=stop} with
  | fail e => simp only [store,indexed,bind_tc_fail] at h ⊢; exact h
  | div => simp only [store,indexed,bind_tc_div] at h ⊢; exact h
  | ok pair =>
    rcases pair with ⟨s,back⟩
    simp only [store,indexed,bind_tc_ok] at h ⊢
    dsimp only at h ⊢
    simpa only [lift,bind_assoc_eq,bind_tc_ok] using h
#print axioms exact
#print axioms store_then
#print Array.update
#print Array.setSlice!
end NBP_Store
