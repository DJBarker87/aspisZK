import RPt_FJo_FourCalls
import RPt_FJi_PrefixValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PrefixBytes
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- Transport strict decoders to the actual selected 608-byte array. -/
theorem value (opening selected : Slice U8) (q : Array U8 608#usize)
    (converted : core.result.Result (Array U8 608#usize) core.array.TryFromSliceError)
    (hs : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      opening {«end»:=608#usize}=ok selected)
    (hc : core.array.TryFromSharedArraySlice.try_from 608#usize selected=ok converted)
    (hp : core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok q) :
    bytesOf q.val=(bytesOf opening.val).take 608 := by
  rw [(FJi_PrefixValue.array selected q converted hc hp).trans
    (FJi_PrefixValue.selected opening selected hs)]
  simp only [bytesOf,List.map_take]
#print axioms value
end AspisR1.FJo_PrefixBytes
end
