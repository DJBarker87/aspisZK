import AspisR1ViewParseProbe.ViewParseRootBinding
import AspisR1ViewParseProbe.ViewParseStrictSecond
import R1PrefixedStateCodec

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ViewParseProbe.ViewParseRootStrictSecond

abbrev State := AspisR1.OpeningRecordCodec.State
abbrev Bytes := AspisR1.OpeningRecordCodec.Bytes

def rootBytesOfArray (a : Array Std.U8 32#usize) : Bytes :=
  a.val.map AspisV8R19.SqueezeOracleBridge.decodeByte

theorem rootBytesOfArray_length (a : Array Std.U8 32#usize) :
    (rootBytesOfArray a).length = 32 := by
  simp [rootBytesOfArray]

theorem rootBytesOfArray_state_roundtrip (a : Array Std.U8 32#usize) :
    rootBytesOfArray a = AspisR1.OpeningRecordCodec.stateBytes
      (FS2.Duplex.stateOfBytes (rootBytesOfArray a)) := by
  have hlen := rootBytesOfArray_length a
  simpa [AspisR1.OpeningRecordCodec.stateBytes] using
    (AspisR1.PrefixedStateCodec.bytes_stateOfBytes (rootBytesOfArray a) hlen).symm

/-- The root stored by a successful two-fold source parse is itself a
fixed-width state encoding. This removes an arbitrary root/rootBytes premise
from the strict second-record result. -/
theorem successful_view_round1_strict_second_from_stored_root
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ root : State, ∃ values : Fin 7 → AspisR1.CanonicalLiteralEcheckStrictSecond.CandidateWide,
      view.folded_root.isSome = true ∧
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          (AspisR1.OpeningRecordCodec.stateBytes root ++
            view.round1.val.map AspisV8R19.SqueezeOracleBridge.decodeByte)) =
        some (root, AspisR1ViewParseProbe.ViewParseStrictSecond.DecodedValues values) := by
  obtain ⟨rootArray, harray⟩ :=
    AspisR1ViewParseProbe.ViewParseRootBinding.successful_parse_has_folded_root
      query_checks input view hparse hfold
  let rootBytes := rootBytesOfArray rootArray
  let root : State := FS2.Duplex.stateOfBytes rootBytes
  have hroot : rootBytes = AspisR1.OpeningRecordCodec.stateBytes root := by
    simpa [root, rootBytes] using rootBytesOfArray_state_roundtrip rootArray
  obtain ⟨values, hdecode⟩ :=
    AspisR1ViewParseProbe.ViewParseStrictSecond.successful_view_round1_is_strict_second
      query_checks input view hparse hfold root rootBytes hroot
  have hdecodeRoot := hdecode
  rw [hroot] at hdecodeRoot
  refine ⟨root, values, ?_, hdecodeRoot⟩
  rw [harray]
  rfl

#print axioms rootBytesOfArray_length
#print axioms rootBytesOfArray_state_roundtrip
#print axioms successful_view_round1_strict_second_from_stored_root

end AspisR1ViewParseProbe.ViewParseRootStrictSecond
