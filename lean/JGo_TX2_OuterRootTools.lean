import Aeneas
set_option autoImplicit false
namespace AspisR1.JGo_TX2_OuterRootTools
open Aeneas Aeneas.Std Result
abbrev Root := Array U8 32#usize
abbrev Unwrap := core.result.Result Root Unit → Result Root

def get (proof : Slice U8) (start stop : Result Usize) (unwrap : Unwrap) : Result Root := do
  let start ← start
  let stop ← stop
  let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=start,«end»:=stop}
  let array ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes
  unwrap array

theorem source (proof bytes : Slice U8) (root : Root)
    (start stop : Result Usize) (unwrap : Unwrap)
    (hs : start=ok 7751#usize) (he : stop=ok 7783#usize)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok bytes)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes=ok (.Ok root))
    (unwrapped : unwrap (.Ok root)=ok root) : get proof start stop unwrap=ok root := by
  unfold get
  rw [hs,bind_tc_ok,he,bind_tc_ok,read,bind_tc_ok,copy,bind_tc_ok,unwrapped]
#print axioms source
end AspisR1.JGo_TX2_OuterRootTools
