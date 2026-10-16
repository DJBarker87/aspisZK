import AspisR1ViewParseProbe.ViewParseRootFrameSource
import AspisR1ViewParseProbe.ParseShapeRound1Span
import AspisR1ViewParseProbe.ParseSuccessRound1Index

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ViewParseProbe.ViewParseRootRound1SourceFrame

private theorem indexed_range_is_source_slice
    (input : Slice Std.U8) (start finish : Std.Usize) (out : Slice Std.U8)
    (hindex : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
      { start := start, «end» := finish } = ok out) :
    out.val = input.val.slice start finish := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := start, «end» := finish } input = ok out at hindex
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hindex
  split at hindex
  · have hout := Result.ok.inj hindex
    simpa using (congrArg (fun s : Slice Std.U8 => s.val) hout).symm
  · cases hindex

/-- Both parts of the accepted `.second` frame are tied to exact intervals of
the caller's input. The root is copied from the parser's checked root slice;
the round-one section is the same slice returned and echecked by the parser. -/
theorem successful_parse_strict_second_frame_uses_input_intervals
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray : Array Std.U8 32#usize, ∃ rootStart rootEnd : Std.Usize,
    ∃ round1Start round1End : Std.Usize, ∃ root : AspisR1.OpeningRecordCodec.State,
    ∃ values : Fin 7 → AspisR1.CanonicalLiteralEcheckStrictSecond.CandidateWide,
      view.folded_root = some rootArray ∧
      rootArray.val = input.val.slice rootStart rootEnd ∧
      view.round1.val = input.val.slice round1Start round1End ∧
      round1End.val - round1Start.val = 224 ∧
      root = FS2.Duplex.stateOfBytes
        ((input.val.slice rootStart rootEnd).map
          AspisV8R19.SqueezeOracleBridge.decodeByte) ∧
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          (((input.val.slice rootStart rootEnd).map
              AspisV8R19.SqueezeOracleBridge.decodeByte) ++
            ((input.val.slice round1Start round1End).map
              AspisV8R19.SqueezeOracleBridge.decodeByte))) =
        some (root, AspisR1ViewParseProbe.ViewParseStrictSecond.DecodedValues values) := by
  obtain ⟨rootArray, rootStart, rootEnd, root, values,
      hroot, hrootBytes, hrootState, hdecode⟩ :=
    AspisR1ViewParseProbe.ViewParseRootFrameSource.successful_parse_binds_root_frame_to_input
      query_checks input view hparse hfold
  obtain ⟨hecheck, shape, hshape, hroundIndex, hvariant⟩ :=
    AspisR1ViewParseProbe.ParseSuccessRound1Index.parse_success_round1_index
      query_checks input view hparse hfold
  have hshapeFold : transport.Variant.folds shape.variant = ok 2#usize := by
    simpa [hvariant] using hfold
  have hroundWidth :=
    AspisR1ViewParseProbe.ParseShapeRound1Span.parse_shape_round1_span
      input shape hshape hshapeFold
  have hroundBytes := indexed_range_is_source_slice input shape.round1_start
    shape.round1_end view.round1 hroundIndex
  have hdecode' := hdecode
  rw [hroundBytes] at hdecode'
  exact ⟨rootArray, rootStart, rootEnd, shape.round1_start, shape.round1_end,
    root, values, hroot, hrootBytes, hroundBytes, hroundWidth, hrootState, hdecode'⟩

#print axioms successful_parse_strict_second_frame_uses_input_intervals

end AspisR1ViewParseProbe.ViewParseRootRound1SourceFrame
