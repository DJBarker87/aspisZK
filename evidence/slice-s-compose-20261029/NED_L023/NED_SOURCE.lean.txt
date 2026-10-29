import NBG_Atomic
set_option autoImplicit false
noncomputable section
namespace NBP_Read
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

def chunk {N W : Usize} (bytes : Array U8 N) (start : Nat)
    (bound : start+W.val ≤ N.val) : Array U8 W :=
  ⟨(bytes.val.drop start).take W.val, by
    simp only [List.length_take,List.length_drop,bytes.property]
    omega⟩

theorem copy {N W : Usize} (bytes : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    (do
      let s ← core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        bytes {start,«end»:=stop}
      let r ← core.array.TryFromArrayCopySlice.try_from W core.marker.CopyU8 s
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy W core.marker.CopyU8) r) =
      ok (chunk bytes start.val (by omega)) := by
  have room : W.val ≤ N.val-start.val := by omega
  simp [room,core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,
    Slice.length,Slice.len,order,bound,bytes.property,
    core.array.TryFromArrayCopySlice.try_from,NBG_Atomic.unwrap_ok,
    List.slice,List.length_take,List.length_drop,width,chunk]
#print axioms copy
end NBP_Read
