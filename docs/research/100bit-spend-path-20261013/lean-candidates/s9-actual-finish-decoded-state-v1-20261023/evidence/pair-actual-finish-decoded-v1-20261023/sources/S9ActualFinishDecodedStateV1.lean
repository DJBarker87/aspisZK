import S9ActualFinishWordFormulaV1
import S9ActualEbyKBackendTransportV1
import S9ActualPairWideCanonicalV1
import S4TailFinishFieldRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualFinishDecodedStateV1
open AspisR1S9ActualEbyKBackendTransportV1

/-- The existing native/CurrentWide and backend/S4 maps copy the same eight
words. No arithmetic or source success premise is involved. -/
theorem native_current_coordinates (out : NativeW) :
    AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE (toSourceWide out) =
      AspisR1S9ActualPairWideCanonicalV1.toCurrent out := by rfl

/-- SAME actual finish output words have exactly the residues of the SAME
original accumulator cells. All-U64 source reducer correctness was proved
separately; neither history/count bounds nor child successes are assumed. -/
theorem actual_finish_success_residue_words
    (final : fast_pairing.EbyKDot) (out : NativeW)
    (hfinish : fast_pairing.EbyKDot.finish final = .ok out) :
    (AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords
      (toSourceWide out)).map (fun w => w.val) =
    (((toSourceState final).c0.sums.val ++ (toSourceState final).c1.sums.val).map
      (fun x => x.val % AspisV8R17.RawReducer.P)) := by
  have hwords := AspisR1S9ActualFinishWordFormulaV1.actual_finish_success_word_list
    final out hfinish
  have hvalues := congrArg (List.map (fun w : U32 => w.val)) hwords
  change (AspisR1S9ActualFinishWordFormulaV1.nativeWords out).map (fun w => w.val) =
    (final.c0.sums.val ++ final.c1.sums.val).map
      (fun x => x.val % AspisV8R17.RawReducer.P)
  simpa only [List.map_map,Function.comp_def,
    AspisR1S9ActualReduceWordSourceV1.word,
    AspisR1CanonicalDotFinish.Proof.canonicalWord_val] using hvalues

/-- Universal actual native finish decoded value: all state/count values,
no input-canonicality, no history, no accepted-trace, no state-range or
independent model-finish success premise. The SAME final state is retained. -/
theorem actual_finish_success_decodes_state
    (final : fast_pairing.EbyKDot) (out : NativeW)
    (hfinish : fast_pairing.EbyKDot.finish final = .ok out) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent out) =
    AspisR1FastDotsTailFieldProductRootV1.decodeState
      (AspisR1FastDotsPushProductTraceRootV1.stateValue (toSourceState final)) := by
  have hd := AspisR1FastDotsTailFinishFieldRootV1.finish_words_decode_state
    (toSourceState final) (toSourceWide out)
    (actual_finish_success_residue_words final out hfinish)
  simpa only [native_current_coordinates] using hd

/-- Direct consumer of the already-proved product-state equation for this
SAME final accumulator; no replacement final-state witness is introduced. -/
theorem actual_finish_success_product_sum
    (final : fast_pairing.EbyKDot) (out : NativeW)
    (ps : List (AspisR1FastDotsPushProductTraceRootV1.Wide ×
      AspisR1FastDotsPushProductTraceRootV1.QM))
    (hfinish : fast_pairing.EbyKDot.finish final = .ok out)
    (hproduct : AspisR1FastDotsTailFieldProductRootV1.decodeState
      (AspisR1FastDotsPushProductTraceRootV1.stateValue (toSourceState final)) =
      AspisR1FastDotsTailFieldProductRootV1.productSum ps) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent out) =
      AspisR1FastDotsTailFieldProductRootV1.productSum ps :=
  (actual_finish_success_decodes_state final out hfinish).trans hproduct

#print axioms native_current_coordinates
#print axioms actual_finish_success_residue_words
#print axioms actual_finish_success_decodes_state
#print axioms actual_finish_success_product_sum
end AspisR1S9ActualFinishDecodedStateV1
