import NED_ReadDomains
set_option autoImplicit false
namespace NED_StatementReadWindows
open Aeneas Aeneas.Std Result
theorem master (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=8#usize,«end»:=40#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 8 (by decide))) :=
  NED_ReadDomains.converted bytes 8#usize 40#usize (by decide) (by decide) (by decide)
#print axioms master
theorem checkpoint (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=40#usize,«end»:=72#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 40 (by decide))) :=
  NED_ReadDomains.converted bytes 40#usize 72#usize (by decide) (by decide) (by decide)
#print axioms checkpoint
theorem lane (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=72#usize,«end»:=104#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 72 (by decide))) :=
  NED_ReadDomains.converted bytes 72#usize 104#usize (by decide) (by decide) (by decide)
#print axioms lane
theorem sequence (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=104#usize,«end»:=112#usize}
        core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=8#usize) bytes 104 (by decide))) :=
  NED_ReadDomains.converted bytes 104#usize 112#usize (by decide) (by decide) (by decide)
#print axioms sequence
theorem anchor (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=112#usize,«end»:=144#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 112 (by decide))) :=
  NED_ReadDomains.converted bytes 112#usize 144#usize (by decide) (by decide) (by decide)
#print axioms anchor
theorem late (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=144#usize,«end»:=1664#usize}
        core.array.TryFromArrayCopySlice.try_from 1520#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=1520#usize) bytes 144 (by decide))) :=
  NED_ReadDomains.converted bytes 144#usize 1664#usize (by decide) (by decide) (by decide)
#print axioms late
theorem payment (bytes : Array U8 1880#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=1664#usize,«end»:=1880#usize}
        core.array.TryFromArrayCopySlice.try_from 216#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=216#usize) bytes 1664 (by decide))) :=
  NED_ReadDomains.converted bytes 1664#usize 1880#usize (by decide) (by decide) (by decide)
#print axioms payment
end NED_StatementReadWindows
