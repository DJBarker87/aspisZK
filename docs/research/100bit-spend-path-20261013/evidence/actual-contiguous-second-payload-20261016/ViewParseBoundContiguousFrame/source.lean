import AspisR1ViewParseProbe.ViewParseRootSliceBytes
import AspisR1ViewParseProbe.ViewParseRootStrictSecondBound

/-! One joint witness binds actual parser bytes, source interval adjacency,
fixed widths and strict second-record decoding. The interval identities are
exported together; independently chosen existential offsets are not joined. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ViewParseProbe.ViewParseBoundContiguousFrame

private theorem range_index_facts (input out : Slice U8) (start finish : Usize)
    (hindex : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      input { start := start, «end» := finish } = ok out) :
    start.val ≤ finish.val ∧ finish.val ≤ input.val.length ∧
      out.val = input.val.slice start finish := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := start, «end» := finish } input = ok out at hindex
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hindex
  split at hindex
  · rename_i hbound
    have hstart : start.val ≤ finish.val := by simpa only [UScalar.le_equiv] using hbound.1
    have hfinish : finish.val ≤ input.val.length := by
      simpa only [UScalar.le_equiv, Slice.length] using hbound.2
    have hout := Result.ok.inj hindex
    exact ⟨hstart, hfinish, by
      simpa using (congrArg (fun s : Slice U8 => s.val) hout).symm⟩
  · cases hindex

private theorem add_val {a b c : Usize} (h : (a + b : Result Usize) = ok c) :
    c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  rw [h] at he
  exact he.2.1

theorem successful_parse_has_bound_contiguous_second_frame
    (query_checks : Slice U8 → transport.Variant → Result (core.result.Result Unit verifier.Error))
    (input : Slice U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input = ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray : Array U8 32#usize, ∃ rootStart rootEnd roundEnd : Usize,
    ∃ root : AspisR1.OpeningRecordCodec.State,
    ∃ values : Fin 7 → AspisR1.CanonicalLiteralEcheckStrictSecond.CandidateWide,
      view.folded_root = some rootArray ∧
      rootArray.val = input.val.slice rootStart rootEnd ∧
      view.round1.val = input.val.slice rootEnd roundEnd ∧
      rootEnd.val = rootStart.val + 32 ∧
      roundEnd.val = rootEnd.val + 224 ∧
      rootStart.val ≤ rootEnd.val ∧ rootEnd.val ≤ roundEnd.val ∧ roundEnd.val ≤ input.val.length ∧
      root = FS2.Duplex.stateOfBytes
        (rootArray.val.map AspisV8R19.SqueezeOracleBridge.decodeByte) ∧
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          (((input.val.slice rootStart rootEnd).map AspisV8R19.SqueezeOracleBridge.decodeByte) ++
            ((input.val.slice rootEnd roundEnd).map AspisV8R19.SqueezeOracleBridge.decodeByte))) =
        some (root, AspisR1ViewParseProbe.ViewParseStrictSecond.DecodedValues values) := by
  obtain ⟨rootArray, rootStart, rootEnd, rootSlice, tryResult,
      hroot, hadd, hindex, htry, hmap, shape, hshape, hrootStart⟩ :=
    AspisR1ViewParseProbe.ViewParseRootSlice.successful_parse_exposes_root_source_slice
      query_checks input view hparse hfold
  have hinner : tryResult = core.result.Result.Ok rootArray := by
    cases tryResult with
    | Ok inner =>
      have houter : (ok (core.result.Result.Ok inner) :
          Result (core.result.Result (Array U8 32#usize) verifier.Error)) =
          ok (core.result.Result.Ok rootArray) := by
        simpa [core.result.Result.map_err] using hmap
      have heq := core.result.Result.Ok.inj (Result.ok.inj houter)
      subst inner
      rfl
    | Err e =>
      cases hcall : verifier.View.parse.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once () e with
      | ok mapped => simp [core.result.Result.map_err, hcall] at hmap
      | fail err => simp [core.result.Result.map_err, hcall] at hmap
      | div => simp [core.result.Result.map_err, hcall] at hmap
  have hconverted : core.array.TryFromSharedArraySlice.try_from 32#usize rootSlice =
      ok (core.result.Result.Ok rootArray) := by rw [htry, hinner]
  have hcopy := AspisR1ViewParseProbe.ViewParseRootSliceBytes.try_from_success_preserves_bytes rootSlice rootArray hconverted
  obtain ⟨hrOrder, hrBound, hrBytes⟩ := range_index_facts input rootSlice rootStart rootEnd hindex
  have hrootInput := hcopy.trans hrBytes
  obtain ⟨_hecheck, shape2, hshape2, hroundIndex, hvariant⟩ :=
    AspisR1ViewParseProbe.ParseSuccessRound1Index.parse_success_round1_index query_checks input view hparse hfold
  have hshapeEq : shape = shape2 :=
    core.result.Result.Ok.inj (Result.ok.inj (hshape.symm.trans hshape2))
  subst shape2
  obtain ⟨base, hbase, hroundStart, hroundWidth⟩ :=
    AspisR1ViewParseProbe.ParseShapeRound1Root.parse_shape_round1_root_and_start input shape hshape
      (by simpa only [hvariant] using hfold)
  have hbaseEq : base = rootStart := Option.some.inj (hbase.symm.trans hrootStart)
  subst base
  have hEnd : rootEnd.val = rootStart.val + 32 := by simpa using add_val hadd
  have hStart : shape.round1_start.val = rootStart.val + 32 := by simpa using hroundStart
  have hAdjacent : shape.round1_start = rootEnd := UScalar.eq_of_val_eq (hStart.trans hEnd.symm)
  rw [hAdjacent] at hroundIndex hroundWidth
  obtain ⟨hroundOrder, hroundBound, hroundBytes⟩ :=
    range_index_facts input view.round1 rootEnd shape.round1_end hroundIndex
  have hRoundEnd : shape.round1_end.val = rootEnd.val + 224 := by omega
  obtain ⟨rootArray2, root, values, hroot2, hstate, hdecode⟩ :=
    AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.successful_view_round1_strict_second_with_root_binding
      query_checks input view hparse hfold
  have hrootArrayEq : rootArray2 = rootArray := Option.some.inj (hroot2.symm.trans hroot)
  subst rootArray2
  have hrootBytes : AspisR1.OpeningRecordCodec.stateBytes root =
      AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray rootArray := by
    rw [hstate]
    exact (AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray_state_roundtrip rootArray).symm
  rw [hrootBytes] at hdecode
  refine ⟨rootArray, rootStart, rootEnd, shape.round1_end, root, values,
    hroot, hrootInput, hroundBytes, hEnd, hRoundEnd, hrOrder, hroundOrder, hroundBound, ?_, ?_⟩
  · simpa only [AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray] using hstate
  · simpa only [AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray,
      hrootInput, hroundBytes] using hdecode

#print axioms successful_parse_has_bound_contiguous_second_frame
end AspisR1ViewParseProbe.ViewParseBoundContiguousFrame
