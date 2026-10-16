import AspisR1ViewParseProbe.ViewParseRootSlice

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1ViewParseProbe.ViewParseRootSliceBytes

/-- Successful fixed-width conversion copies the source slice bytes into the
returned array. This is the transparent Aeneas model for Rust's
`TryFrom<&[u8]> for [u8; 32]`. -/
theorem try_from_success_preserves_bytes
    (s : Slice Std.U8) (a : Array Std.U8 32#usize)
    (h : core.array.TryFromSharedArraySlice.try_from 32#usize s =
      ok (core.result.Result.Ok a)) :
    a.val = s.val := by
  unfold core.array.TryFromSharedArraySlice.try_from at h
  split at h
  · have houter := Result.ok.inj h
    have harr := core.result.Result.Ok.inj houter
    exact (congrArg (fun x : Array Std.U8 32#usize => x.val) harr).symm
  · simp at h

/-- The parser's successful root conversion preserves the actual source slice,
and the source slice is the interval selected by the parser's checked index. -/
theorem successful_root_array_copies_source_slice
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray rootStart endRoot rootSlice,
      view.folded_root = some rootArray ∧
      (rootStart + 32#usize : Result Std.Usize) = ok endRoot ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
        { start := rootStart, «end» := endRoot } = ok rootSlice ∧
      rootArray.val = rootSlice.val := by
  obtain ⟨rootArray, rootStart, endRoot, rootSlice, tryResult,
      hroot, hend, hindex, htry, hmap, _hshapeData⟩ :=
    AspisR1ViewParseProbe.ViewParseRootSlice.successful_parse_exposes_root_source_slice
      query_checks input view hparse hfold
  have hinner : tryResult = core.result.Result.Ok rootArray := by
    cases tryResult with
    | Ok inner =>
        have houter :
            (ok (core.result.Result.Ok inner) :
              Result (core.result.Result (Array Std.U8 32#usize) verifier.Error)) =
            ok (core.result.Result.Ok rootArray) := by
          simpa [core.result.Result.map_err] using hmap
        have hin := Result.ok.inj houter
        have hin' := core.result.Result.Ok.inj hin
        subst inner
        rfl
    | Err e =>
        cases hcall : verifier.View.parse.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once () e with
        | ok mapped => simp [core.result.Result.map_err, hcall] at hmap
        | fail err => simp [core.result.Result.map_err, hcall] at hmap
        | div => simp [core.result.Result.map_err, hcall] at hmap
  have hconverted :
      core.array.TryFromSharedArraySlice.try_from 32#usize rootSlice =
        ok (core.result.Result.Ok rootArray) := by
    rw [htry, hinner]
  have hcopy := try_from_success_preserves_bytes rootSlice rootArray hconverted
  exact ⟨rootArray, rootStart, endRoot, rootSlice, hroot, hend, hindex, hcopy⟩

#print axioms try_from_success_preserves_bytes
#print axioms successful_root_array_copies_source_slice

end AspisR1ViewParseProbe.ViewParseRootSliceBytes
