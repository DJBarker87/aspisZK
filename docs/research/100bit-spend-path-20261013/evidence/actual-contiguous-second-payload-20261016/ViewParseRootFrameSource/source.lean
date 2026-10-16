import AspisR1ViewParseProbe.ViewParseRootSourceInterval
import AspisR1ViewParseProbe.ViewParseRootStrictSecondBound

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ViewParseProbe.ViewParseRootFrameSource

abbrev State := AspisR1.OpeningRecordCodec.State
abbrev CandidateWide := AspisR1.CanonicalLiteralEcheckStrictSecond.CandidateWide

/-- The strict second-record frame produced by a successful parser call uses
the root bytes copied from the actual input interval, followed by the actual
returned round-one slice. -/
theorem successful_parse_binds_root_frame_to_input
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray : Array Std.U8 32#usize, ∃ rootStart endRoot : Std.Usize,
    ∃ root : State,
    ∃ values : Fin 7 → CandidateWide,
      view.folded_root = some rootArray ∧
      rootArray.val = input.val.slice rootStart endRoot ∧
      root = FS2.Duplex.stateOfBytes
        ((input.val.slice rootStart endRoot).map
          AspisV8R19.SqueezeOracleBridge.decodeByte) ∧
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          (((input.val.slice rootStart endRoot).map
              AspisV8R19.SqueezeOracleBridge.decodeByte) ++
            view.round1.val.map AspisV8R19.SqueezeOracleBridge.decodeByte)) =
        some (root, AspisR1ViewParseProbe.ViewParseStrictSecond.DecodedValues values) := by
  obtain ⟨sourceArray, rootStart, endRoot, hsourceRoot, hsourceBytes⟩ :=
    AspisR1ViewParseProbe.ViewParseRootSourceInterval.successful_root_array_is_input_interval
      query_checks input view hparse hfold
  obtain ⟨boundArray, root, values, hboundRoot, hrootState, hdecode⟩ :=
    AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.successful_view_round1_strict_second_with_root_binding
      query_checks input view hparse hfold
  have harr : sourceArray = boundArray := by
    exact Option.some.inj (hsourceRoot.symm.trans hboundRoot)
  have hsourceBytes' := hsourceBytes
  rw [harr] at hsourceBytes'
  have hbytes :
      AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray boundArray =
        (input.val.slice rootStart endRoot).map
          AspisV8R19.SqueezeOracleBridge.decodeByte := by
    exact congrArg (List.map AspisV8R19.SqueezeOracleBridge.decodeByte) hsourceBytes'
  have hstateBytes : AspisR1.OpeningRecordCodec.stateBytes root =
      AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray boundArray := by
    rw [hrootState]
    exact (AspisR1ViewParseProbe.ViewParseRootStrictSecondBound.rootBytesOfArray_state_roundtrip
      boundArray).symm
  have hdecodeInput := hdecode
  rw [hstateBytes, hbytes] at hdecodeInput
  have hrootInput := hrootState
  rw [hbytes] at hrootInput
  exact ⟨boundArray, rootStart, endRoot, root, values,
    hboundRoot, hsourceBytes', hrootInput, hdecodeInput⟩

#print axioms successful_parse_binds_root_frame_to_input

end AspisR1ViewParseProbe.ViewParseRootFrameSource
