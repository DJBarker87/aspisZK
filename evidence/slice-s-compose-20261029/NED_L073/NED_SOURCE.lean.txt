import NED_ReadDomains
set_option autoImplicit false
namespace NED_LateReadWindows
open Aeneas Aeneas.Std Result
theorem header_width (bytes : Array U8 1520#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=10#usize,«end»:=12#usize}
        core.array.TryFromArrayCopySlice.try_from 2#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=2#usize) bytes 10 (by decide))) :=
  NED_ReadDomains.converted bytes 10#usize 12#usize (by decide) (by decide) (by decide)
#print axioms header_width
theorem snapshot_width (bytes : Array U8 1520#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=12#usize,«end»:=16#usize}
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=4#usize) bytes 12 (by decide))) :=
  NED_ReadDomains.converted bytes 12#usize 16#usize (by decide) (by decide) (by decide)
#print axioms snapshot_width
theorem afterstate_width (bytes : Array U8 1520#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=16#usize,«end»:=20#usize}
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=4#usize) bytes 16 (by decide))) :=
  NED_ReadDomains.converted bytes 16#usize 20#usize (by decide) (by decide) (by decide)
#print axioms afterstate_width
theorem total_width (bytes : Array U8 1520#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=20#usize,«end»:=24#usize}
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=4#usize) bytes 20 (by decide))) :=
  NED_ReadDomains.converted bytes 20#usize 24#usize (by decide) (by decide) (by decide)
#print axioms total_width
theorem snapshot (bytes : Array U8 1520#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=32#usize,«end»:=832#usize}
        core.array.TryFromArrayCopySlice.try_from 800#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=800#usize) bytes 32 (by decide))) :=
  NED_ReadDomains.converted bytes 32#usize 832#usize (by decide) (by decide) (by decide)
#print axioms snapshot
theorem afterstate (bytes : Array U8 1520#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=832#usize,«end»:=1520#usize}
        core.array.TryFromArrayCopySlice.try_from 688#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=688#usize) bytes 832 (by decide))) :=
  NED_ReadDomains.converted bytes 832#usize 1520#usize (by decide) (by decide) (by decide)
#print axioms afterstate
end NED_LateReadWindows
