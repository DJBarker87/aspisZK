import NBP_Read
set_option autoImplicit false
namespace NED_ReadDomains
open Aeneas Aeneas.Std Result

/-- The reached slice conversion is Ok on the SAME selected bytes; the
callee's unwrap domain is proved, not inferred from a successful parent. -/
theorem converted {N W : Usize} (bytes : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start,«end»:=stop}
        core.array.TryFromArrayCopySlice.try_from W core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk bytes start.val (by omega))) := by
  have room : W.val ≤ N.val-start.val := by omega
  simp [room,core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,
    Slice.length,Slice.len,order,bound,bytes.property,
    core.array.TryFromArrayCopySlice.try_from,List.slice,List.length_take,
    List.length_drop,width,NBP_Read.chunk]

theorem bytes_retained {N W : Usize} (bytes : Array U8 N) (start : Nat)
    (bound : start+W.val ≤ N.val) :
    (NBP_Read.chunk (W:=W) bytes start bound).val = (bytes.val.drop start).take W.val := rfl

#print axioms converted
#print axioms bytes_retained
end NED_ReadDomains
