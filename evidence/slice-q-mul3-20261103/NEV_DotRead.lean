import NEG_DotAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NEV_DotRead
open Aeneas Aeneas.Std Result
def read (q : Array U8 608#usize) (slot term : Usize) : Result U32 := do
  let i ← slot * 120#usize
  let i1 ← term * 4#usize
  let i2 ← i + i1
  let i3 ← i + i1
  let i4 ← i3 + 4#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start:=i2,«end»:=i4}
  let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let o ← FIp_DotDecode.field.M31.from_le_bytes a
  core.option.Option.unwrap o

end AspisR1.NEV_DotRead
end
