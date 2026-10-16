import AspisR1ViewParseProbe.ViewParseRootSliceBytes

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1ViewParseProbe.ViewParseRootSourceInterval

/-- The array retained by the parser is exactly the bytes in the checked
source interval. This exposes byte provenance, not just the successful
fixed-width conversion. -/
theorem successful_root_array_is_input_interval
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray : Array Std.U8 32#usize, ∃ rootStart endRoot : Std.Usize,
      view.folded_root = some rootArray ∧
      rootArray.val = input.val.slice rootStart endRoot := by
  obtain ⟨rootArray, rootStart, endRoot, rootSlice,
      hroot, hend, hindex, hcopy⟩ :=
    AspisR1ViewParseProbe.ViewParseRootSliceBytes.successful_root_array_copies_source_slice
      query_checks input view hparse hfold
  have hslice : rootSlice.val = input.val.slice rootStart endRoot := by
    have hidx := hindex
    change core.slice.index.SliceIndexRangeUsizeSlice.index
      { start := rootStart, «end» := endRoot } input = ok rootSlice at hidx
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hidx
    split at hidx
    · have hout := Result.ok.inj hidx
      simpa using (congrArg (fun s : Slice Std.U8 => s.val) hout).symm
    · cases hidx
  exact ⟨rootArray, rootStart, endRoot, hroot, hcopy.trans hslice⟩

#print axioms successful_root_array_is_input_interval

end AspisR1ViewParseProbe.ViewParseRootSourceInterval
