import NED_ReadDomains
set_option autoImplicit false
namespace NED_RequestReadWindows
open Aeneas Aeneas.Std Result
theorem profile (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=8#usize,«end»:=40#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 8 (by decide))) :=
  NED_ReadDomains.converted bytes 8#usize 40#usize (by decide) (by decide) (by decide)
#print axioms profile
theorem release (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=40#usize,«end»:=72#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 40 (by decide))) :=
  NED_ReadDomains.converted bytes 40#usize 72#usize (by decide) (by decide) (by decide)
#print axioms release
theorem pool_program (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=72#usize,«end»:=104#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 72 (by decide))) :=
  NED_ReadDomains.converted bytes 72#usize 104#usize (by decide) (by decide) (by decide)
#print axioms pool_program
theorem payment (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=104#usize,«end»:=320#usize}
        core.array.TryFromArrayCopySlice.try_from 216#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=216#usize) bytes 104 (by decide))) :=
  NED_ReadDomains.converted bytes 104#usize 320#usize (by decide) (by decide) (by decide)
#print axioms payment
end NED_RequestReadWindows
