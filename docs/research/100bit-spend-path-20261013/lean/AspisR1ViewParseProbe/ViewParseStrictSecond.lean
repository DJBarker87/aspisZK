import AspisR1ViewParseProbe.ParseSuccessRound1Length
import AspisR1ViewParseProbe.ViewEcheckRound1Transfer
import CanonicalLiteralEcheckStrictSecondChunkFacts2

set_option autoImplicit false

namespace AspisR1ViewParseProbe.ViewParseStrictSecond
open Aeneas Aeneas.Std Result

abbrev CandidateWide := AspisR1.CanonicalLiteralEcheckStrictSecond.CandidateWide
abbrev State := AspisR1.CanonicalLiteralEcheckStrictSecond.State
abbrev Bytes := AspisR1.CanonicalLiteralEcheckStrictSecond.Bytes
abbrev DecodedValues := AspisR1.CanonicalLiteralEcheckStrictSecond.decodedValues

theorem successful_view_round1_is_strict_second
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize)
    (root : State) (rootBytes : Bytes)
    (hroot : rootBytes = AspisR1.OpeningRecordCodec.stateBytes root) :
    ∃ values : Fin 7 → CandidateWide,
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          (rootBytes ++ view.round1.val.map AspisV8R19.SqueezeOracleBridge.decodeByte)) =
        some (root, DecodedValues values) := by
  have hsuccess := AspisR1ViewParseProbe.ParseSuccessRound1Length.parse_success_round1_length
    query_checks input view hparse hfold
  have hlen : view.round1.val.length = 224 := by
    simpa [Slice.len, Slice.length] using hsuccess.2
  have hcheck := AspisR1ViewParseProbe.ViewEcheckRound1Transfer.echeck_round1_success_transfer
    view.round1 hsuccess.1
  exact AspisR1.CanonicalLiteralEcheckStrictSecond.echeck_success_strict_second_decode
    root rootBytes view.round1 hroot hlen hcheck

#print axioms successful_view_round1_is_strict_second

end AspisR1ViewParseProbe.ViewParseStrictSecond
