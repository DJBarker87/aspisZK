import NED_ReadDomains
set_option autoImplicit false
namespace NED_AfterstateReadWindows
open Aeneas Aeneas.Std Result
theorem index (bytes : Array U8 688#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=8#usize,«end»:=16#usize}
        core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=8#usize) bytes 8 (by decide))) :=
  NED_ReadDomains.converted bytes 8#usize 16#usize (by decide) (by decide) (by decide)
#print axioms index
theorem root (bytes : Array U8 688#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=16#usize,«end»:=48#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 16 (by decide))) :=
  NED_ReadDomains.converted bytes 16#usize 48#usize (by decide) (by decide) (by decide)
#print axioms root
end NED_AfterstateReadWindows
