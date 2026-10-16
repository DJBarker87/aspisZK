import AspisR1ViewParseProbe.ViewParseRootSlice
import AspisR1ViewParseProbe.ParseShapeRound1Root

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ViewParseProbe.ViewParseContiguousIntervals

private theorem add_val {a b c : Usize}
    (h : UScalar.add a b = Result.ok c) : c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  have h' : (a + b : Result Usize) = Result.ok c := by
    change UScalar.add a b = Result.ok c
    exact h
  rw [h'] at he
  exact he.2.1

/-- For a successful two-fold parse, the parser's fixed-width root interval ends
at the exact start of the returned round-one interval. The root interval has
width 32 and round one has width 224. -/
theorem successful_parse_intervals_are_contiguous
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootStart rootEnd round1Start round1End : Std.Usize,
      (rootStart + 32#usize : Result Std.Usize) = ok rootEnd ∧
      rootEnd.val = round1Start.val ∧
      round1End.val - round1Start.val = 224 := by
  obtain ⟨rootArray, rootStart, rootEnd, rootSlice, tryResult,
      hroot, hadd, hindex, htry, hmap, hshapeData⟩ :=
    AspisR1ViewParseProbe.ViewParseRootSlice.successful_parse_exposes_root_source_slice
      query_checks input view hparse hfold
  obtain ⟨shape, hshape, hrootStart⟩ := hshapeData
  obtain ⟨shape2, hindexShape, _, hvariant⟩ :=
    (AspisR1ViewParseProbe.ParseSuccessRound1Index.parse_success_round1_index
      query_checks input view hparse hfold).2
  have hshapeEq : shape = shape2 := by
    have hi : core.result.Result.Ok shape = core.result.Result.Ok shape2 :=
      Result.ok.inj (hshape.symm.trans hindexShape)
    exact core.result.Result.Ok.inj hi
  subst shape2
  obtain ⟨base, hbase, hroundStart, hroundWidth⟩ :=
    AspisR1ViewParseProbe.ParseShapeRound1Root.parse_shape_round1_root_and_start
      input _ hindexShape (by simpa [hvariant] using hfold)
  have hbaseEq : base = rootStart := Option.some.inj (hbase.symm.trans hrootStart)
  subst base
  have hadd' : (UScalar.add rootStart 32#usize) = Result.ok rootEnd := hadd
  have hendVal := add_val hadd'
  refine ⟨rootStart, rootEnd, shape.round1_start, shape.round1_end, hadd, ?_, hroundWidth⟩
  have hendVal' : rootEnd.val = rootStart.val + 32 := by simpa using hendVal
  have hroundStart' : shape.round1_start.val = rootStart.val + 32 := by
    simpa using hroundStart
  exact hendVal'.trans hroundStart'.symm

#print axioms successful_parse_intervals_are_contiguous

end AspisR1ViewParseProbe.ViewParseContiguousIntervals
