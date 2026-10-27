import RPt_FIp_DotsReached
import RPz7_PSem_Slices
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_PrefixValue
open Aeneas Aeneas.Std Result
/-- Successful installed RangeTo uses the SAME literal first608 bytes. -/
theorem selected (q opening608 : Slice U8)
    (run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      q {«end»:=608#usize}=ok opening608) : opening608.val=q.val.take 608 := by
  change core.slice.index.SliceIndexRangeToUsizeSlice.index {«end»:=608#usize} q=ok opening608 at run
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index at run
  split at run
  · cases Result.ok.inj run
    simp only [List.slice,List.drop_zero,Nat.sub_zero,show (608#usize).val=608 from by scalar_tac]
  · cases run

/-- The successful shared-array conversion copies no alternative input bytes. -/
theorem array (opening608 : Slice U8) (a : Array U8 608#usize)
    (r : core.result.Result (Array U8 608#usize) core.array.TryFromSliceError)
    (convert : core.array.TryFromSharedArraySlice.try_from 608#usize opening608=ok r)
    (unwrap : core.result.Result.unwrap core.fmt.DebugTryFromSliceError r=ok a) :
    a.val=opening608.val := by
  unfold core.array.TryFromSharedArraySlice.try_from at convert
  split at convert
  · cases Result.ok.inj convert
    cases Result.ok.inj unwrap
    rfl
  · cases Result.ok.inj convert
    cases unwrap
#print axioms selected
#print axioms array
end AspisR1.FJi_PrefixValue
end
