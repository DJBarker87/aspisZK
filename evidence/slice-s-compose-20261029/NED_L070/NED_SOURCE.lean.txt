import NED_ReadDomains
set_option autoImplicit false
namespace NED_PaymentReadWindows
open Aeneas Aeneas.Std Result
theorem pool (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=8#usize,«end»:=40#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 8 (by decide))) :=
  NED_ReadDomains.converted bytes 8#usize 40#usize (by decide) (by decide) (by decide)
#print axioms pool
theorem deployment (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=40#usize,«end»:=72#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 40 (by decide))) :=
  NED_ReadDomains.converted bytes 40#usize 72#usize (by decide) (by decide) (by decide)
#print axioms deployment
theorem sequence (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=72#usize,«end»:=80#usize}
        core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=8#usize) bytes 72 (by decide))) :=
  NED_ReadDomains.converted bytes 72#usize 80#usize (by decide) (by decide) (by decide)
#print axioms sequence
theorem anchor (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=80#usize,«end»:=112#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 80 (by decide))) :=
  NED_ReadDomains.converted bytes 80#usize 112#usize (by decide) (by decide) (by decide)
#print axioms anchor
theorem nullifier (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=112#usize,«end»:=144#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 112 (by decide))) :=
  NED_ReadDomains.converted bytes 112#usize 144#usize (by decide) (by decide) (by decide)
#print axioms nullifier
theorem asset (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=144#usize,«end»:=148#usize}
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=4#usize) bytes 144 (by decide))) :=
  NED_ReadDomains.converted bytes 144#usize 148#usize (by decide) (by decide) (by decide)
#print axioms asset
theorem amount (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=148#usize,«end»:=152#usize}
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=4#usize) bytes 148 (by decide))) :=
  NED_ReadDomains.converted bytes 148#usize 152#usize (by decide) (by decide) (by decide)
#print axioms amount
theorem recipient_destination (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=152#usize,«end»:=184#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 152 (by decide))) :=
  NED_ReadDomains.converted bytes 152#usize 184#usize (by decide) (by decide) (by decide)
#print axioms recipient_destination
theorem change (bytes : Array U8 216#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=184#usize,«end»:=216#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 184 (by decide))) :=
  NED_ReadDomains.converted bytes 184#usize 216#usize (by decide) (by decide) (by decide)
#print axioms change
end NED_PaymentReadWindows
