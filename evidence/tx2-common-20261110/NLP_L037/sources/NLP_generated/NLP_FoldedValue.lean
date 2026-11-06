import NLP_FoldedRange
set_option autoImplicit false
noncomputable section
namespace NLP_FoldedValue
open Aeneas Aeneas.Std Result
theorem source (proof selected : Slice U8)
 (r : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
 (root : Array U8 32#usize)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=7751#usize,«end»:=7783#usize}=ok selected)
 (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 selected=ok r)
 (unwrap : core.result.Result.unwrap core.fmt.DebugTryFromSliceError r=ok root) :
 root.val=(proof.val.drop 7751).take 32 := by
 cases r with
 | Err error => cases unwrap
 | Ok actual =>
   have same:=Result.ok.inj unwrap
   subst actual
   exact (NLP_FoldedRange.copied selected root copy).trans (NLP_FoldedRange.selected proof selected range)
set_option pp.proofs false
#print source
#print axioms source
end NLP_FoldedValue
