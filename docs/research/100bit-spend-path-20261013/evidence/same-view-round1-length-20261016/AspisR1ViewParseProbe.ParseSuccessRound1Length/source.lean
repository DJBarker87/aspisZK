import AspisR1ViewParseProbe.ParseSuccessRound1Index
import AspisR1ViewParseProbe.ParseShapeRound1Span
import AspisR1ViewParseProbe.SliceIndexLength

set_option autoImplicit false
open Aeneas Aeneas.Std Result Error

namespace AspisR1ViewParseProbe.ParseSuccessRound1Length

/-- For every query-check implementation, a successful parse with two folds
checks the exact returned round-one slice and gives it the source width 224. -/
theorem parse_success_round1_length
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (bytes : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks bytes =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    verifier.echeck view.round1 false = ok (core.result.Result.Ok ()) ∧
      (Slice.len view.round1).val = 224 := by
  obtain ⟨hecheck, shape, hshape, hindex, hvariant⟩ :=
    AspisR1ViewParseProbe.ParseSuccessRound1Index.parse_success_round1_index
      query_checks bytes view hparse hfold
  have hfoldShape : transport.Variant.folds shape.variant = ok 2#usize := by
    simpa [hvariant] using hfold
  have hspan :=
    AspisR1ViewParseProbe.ParseShapeRound1Span.parse_shape_round1_span
      bytes shape hshape hfoldShape
  have hlen :=
    AspisR1ViewParseProbe.SliceIndexLength.range_index_success_length
      bytes view.round1 shape.round1_start shape.round1_end hindex
  constructor
  · exact hecheck
  · rw [hlen, hspan]

#print axioms parse_success_round1_length

end AspisR1ViewParseProbe.ParseSuccessRound1Length
