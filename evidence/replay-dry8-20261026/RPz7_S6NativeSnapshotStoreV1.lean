import RPz7_S6NativeAfterstateCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeSnapshotStore

def write (output : Slice U8) (start : Nat) (bytes : Array U8 32#usize) : Slice U8 :=
  ⟨output.val.setSlice! start bytes.val, by
    rw [AspisS6SliceFrame.setSlice_length]
    exact output.property⟩

theorem write_length (output : Slice U8) (start : Nat) (bytes : Array U8 32#usize) :
    (write output start bytes).length=output.length := by
  exact AspisS6SliceFrame.setSlice_length _ _ _

def store (output : Slice U8) (start stop : Usize) (bytes : Array U8 32#usize) : Result (Slice U8) := do
  let (slice,back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start,«end»:=stop}
  let source ← lift (Array.to_slice bytes)
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 slice source
  ok (back copied)

theorem store_exact (output : Slice U8) (start stop : Usize) (bytes : Array U8 32#usize)
    (order : start.val≤stop.val) (bound : stop.val≤output.length)
    (width : stop.val-start.val=32) :
    store output start stop bytes=ok (write output start.val bytes) := by
  have room : 32≤output.length-start.val := by omega
  have bs := bytes.property
  simp only [store,core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,Array.to_slice]
  simp [Slice.length,Slice.len,order,bound,core.slice.Slice.copy_from_slice,
    List.slice,width,Nat.min_eq_left room,bs,write,lift]

#print axioms write_length
#print axioms store_exact
end AspisS6NativeSnapshotStore
