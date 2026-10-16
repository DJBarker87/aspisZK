import AspisR1ViewParseProbe.ViewParseBoundContiguousFrame

/-! The exact two parser-returned row30 sections form one checked256-byte
input window, and that same payload has strict second-record decoding. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ViewParseProbe.ViewParseContiguousPayload

theorem adjacent_slices_append {α : Type} (xs : List α) (start middle finish : Nat)
    (hsm : start ≤ middle) (hmf : middle ≤ finish) :
    xs.slice start middle ++ xs.slice middle finish = xs.slice start finish := by
  unfold List.slice
  have hspan : finish - start = (middle - start) + (finish - middle) := by omega
  have hmiddle : start + (middle - start) = middle := by omega
  rw [hspan, List.take_add, List.drop_drop, hmiddle]

theorem successful_parse_strict_second_is_one_source_window
    (query_checks : Slice U8 → transport.Variant → Result (core.result.Result Unit verifier.Error))
    (input : Slice U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input = ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray : Array U8 32#usize, ∃ start finish : Usize,
    ∃ root : AspisR1.OpeningRecordCodec.State,
    ∃ values : Fin 7 → AspisR1.CanonicalLiteralEcheckStrictSecond.CandidateWide,
      view.folded_root = some rootArray ∧
      rootArray.val ++ view.round1.val = input.val.slice start finish ∧
      finish.val = start.val + 256 ∧ finish.val ≤ input.val.length ∧
      (input.val.slice start finish).length = 256 ∧
      root = FS2.Duplex.stateOfBytes (rootArray.val.map AspisV8R19.SqueezeOracleBridge.decodeByte) ∧
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          ((input.val.slice start finish).map AspisV8R19.SqueezeOracleBridge.decodeByte)) =
        some (root, AspisR1ViewParseProbe.ViewParseStrictSecond.DecodedValues values) := by
  obtain ⟨rootArray, start, middle, finish, root, values,
      hroot, hrootBytes, hroundBytes, hRootEnd, hRoundEnd, hsm, hmf, hfinishBound, hstate, hdecode⟩ :=
    AspisR1ViewParseProbe.ViewParseBoundContiguousFrame.successful_parse_has_bound_contiguous_second_frame
      query_checks input view hparse hfold
  have hjoin := adjacent_slices_append input.val start.val middle.val finish.val hsm hmf
  have hpayload : rootArray.val ++ view.round1.val = input.val.slice start finish := by
    rw [hrootBytes, hroundBytes]
    exact hjoin
  have hfinish : finish.val = start.val + 256 := by omega
  have hlength : (input.val.slice start finish).length = 256 := by
    rw [List.slice_length]
    have hspan : finish.val - start.val = 256 := by omega
    rw [hspan]
    exact Nat.min_eq_right (by omega)
  have hjoinMap := congrArg (fun xs : List U8 => xs.map AspisV8R19.SqueezeOracleBridge.decodeByte) hjoin
  simp only [List.map_append] at hjoinMap
  rw [hjoinMap] at hdecode
  exact ⟨rootArray, start, finish, root, values, hroot, hpayload, hfinish, hfinishBound,
    hlength, hstate, hdecode⟩

#print axioms adjacent_slices_append
#print axioms successful_parse_strict_second_is_one_source_window
end AspisR1ViewParseProbe.ViewParseContiguousPayload
