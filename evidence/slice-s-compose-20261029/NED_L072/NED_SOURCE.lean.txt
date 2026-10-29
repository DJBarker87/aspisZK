import NED_ReadDomains
set_option autoImplicit false
namespace NED_SnapshotReadWindows
open Aeneas Aeneas.Std Result
theorem pool (bytes : Array U8 800#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=48#usize,«end»:=80#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 48 (by decide))) :=
  NED_ReadDomains.converted bytes 48#usize 80#usize (by decide) (by decide) (by decide)
#print axioms pool
theorem deployment (bytes : Array U8 800#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=80#usize,«end»:=112#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 80 (by decide))) :=
  NED_ReadDomains.converted bytes 80#usize 112#usize (by decide) (by decide) (by decide)
#print axioms deployment
theorem sequence (bytes : Array U8 800#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=112#usize,«end»:=120#usize}
        core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=8#usize) bytes 112 (by decide))) :=
  NED_ReadDomains.converted bytes 112#usize 120#usize (by decide) (by decide) (by decide)
#print axioms sequence
theorem index (bytes : Array U8 800#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=120#usize,«end»:=128#usize}
        core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=8#usize) bytes 120 (by decide))) :=
  NED_ReadDomains.converted bytes 120#usize 128#usize (by decide) (by decide) (by decide)
#print axioms index
theorem root (bytes : Array U8 800#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=128#usize,«end»:=160#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 128 (by decide))) :=
  NED_ReadDomains.converted bytes 128#usize 160#usize (by decide) (by decide) (by decide)
#print axioms root
end NED_SnapshotReadWindows
