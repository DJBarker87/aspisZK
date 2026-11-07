import PCF_CopyRange
import PCF_ResultAssoc
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_CopyMap

theorem result {B : Type} (f : Slice U8 → B) (data src : Slice U8)
    (r : core.ops.range.Range Usize)
    (bounds : r.start ≤ r.«end» ∧ r.«end».val ≤ data.length)
    (width : src.length = r.«end».val-r.start.val) :
    (do let (window,back) ← core.slice.index.SliceIndexRangeUsizeSlice.index_mut r data
        let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window src
        ok (f (back copied))) = ok (f (data.setSlice! r.start.val src.val)) := by
  have hw := PCF_CopyRange.result data src r bounds width
  have hm := congrArg (fun p : Result (Slice U8) => do let d ← p; ok (f d)) hw
  unfold PCF_CopyRange.write at hm
  generalize hq : core.slice.index.SliceIndexRangeUsizeSlice.index_mut r data = q at hm ⊢
  cases q with
  | fail e => exact hm
  | div => exact hm
  | ok pair =>
    rcases pair with ⟨window,back⟩
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window src
               ok (f (back copied))) = _
    change (do let d ← (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window src; ok (back copied))
               ok (f d)) = _ at hm
    simpa only [← PCF_ResultAssoc.assoc,bind_tc_ok] using hm

#print axioms result
end PCF_CopyMap
